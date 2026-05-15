/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Homogeneous.Basic
import SymmetricIdeals.Homogeneous.MinDeg
import SymmetricIdeals.Homogeneous.Degree
import SymmetricIdeals.Symmetry.Basic
import SymmetricIdeals.Upstream

open MvPolynomial Rename

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped Pointwise

noncomputable
def IsSingleDegGen (I : Ideal (MvPolynomial α R)) :=
  I = Ideal.span (homogeneousSubmoduleI (minDeg I) I)

@[simp]
lemma zero_singleDegGen : IsSingleDegGen (0 : Ideal (MvPolynomial α R)) := by
  simp [IsSingleDegGen]

@[simp]
lemma bot_singleDegGen : IsSingleDegGen (⊥ : Ideal (MvPolynomial α R)) := by
  simp [IsSingleDegGen]

theorem isSingleDegGen_iff : IsSingleDegGen I ↔ ∃ n : ℕ, ∃ S : Set (MvPolynomial α R),
    S ⊆ (homogeneousSubmodule α R n) ∧ I = Ideal.span S := by
  constructor
  · intro h
    use (minDeg I), (homogeneousSubmoduleI (minDeg I) I)
    constructor
    · exact inf_le_left
    · exact h
  · intro ⟨n, S, hS, h⟩
    by_cases! hzS : ∃ p ∈ S, p ≠ 0
    · nth_rw 1 [IsSingleDegGen, h]
      nth_rw 1 [h, minDeg_homog hzS hS]
      refine Submodule.span_eq_span ?_ ?_
      · refine le_trans ?_ Submodule.subset_span
        refine le_inf hS ?_
        simp [h]
      · exact le_trans inf_le_right <| by simp [h]
    · simp_rw [h, Ideal.span_eq_bot.mpr hzS, ← Submodule.zero_eq_bot, zero_singleDegGen]

theorem isSingleDegGen_iff' : IsSingleDegGen I ↔ ∃ S : Set (MvPolynomial α R),
    S ⊆ (homogeneousSubmodule α R (minDeg I) ) ∧ I = Ideal.span S := by
  constructor
  · rw [isSingleDegGen_iff]
    intro ⟨n, S, h, hI⟩
    use S
    constructor
    · by_cases! hS : ∃ p ∈ S, p ≠ 0
      · rwa [hI, minDeg_homog hS h]
      · intro p hp
        simp [hS p hp]
    · exact hI
  · intro h
    rw [isSingleDegGen_iff]
    use minDeg I


@[simp]
lemma top_singleDegGen : IsSingleDegGen (⊤ : Ideal (MvPolynomial α R)) := by
  simp [IsSingleDegGen, Submodule.one_eq_span]

theorem isHomogeneous_of_isSingleDegGen (h : IsSingleDegGen I) :
    Ideal.IsHomogeneous (homogeneousSubmodule α R) I := by
  rw [h]
  refine Ideal.homogeneous_span _ _ ?_
  simp [SetLike.IsHomogeneousElem]
  grind


lemma homogSubI_strictMono (n : ℕ) {I J : Ideal (MvPolynomial α R)} (hmd : minDeg I = minDeg J)
    (hn : minDeg I = n) (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J) (hIJ : I < J) :
    homogeneousSubmoduleI n I < homogeneousSubmoduleI n J := by
  refine lt_of_le_of_ne (homogSubI_monotone n (le_of_lt hIJ)) ?_
  subst hn
  nth_rw 2 [hmd]
  contrapose! hIJ
  rw [hI, hJ, hIJ]
  exact lt_irrefl _

lemma eq_of_homogSubI_eq {I J : Ideal (MvPolynomial α R)}
    (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
    (h : homogeneousSubmoduleI (minDeg I) I = homogeneousSubmoduleI (minDeg J) J) :
    I = J := by
  rw [hI, hJ, h]


@[simp]
lemma homogSubI_span_apply {n m : ℕ} {S : Set (MvPolynomial α R)} (hnm : m ≥ n)
    (h : S ⊆ homogeneousSubmodule α R m) : homogeneousSubmoduleI n (Ideal.span S) =
    if n = m then homogeneousSubmoduleI m (Ideal.span S) else 0 := by
  by_cases! heq : n = m
  · simp [heq]
  · simp only [heq, reduceIte]
    by_cases! hS : ∃ p ∈ S, p ≠ 0
    · suffices minDeg (Ideal.span S) > n by
        apply Nat.notMem_of_lt_sInf at this
        simpa using this
      rw [minDeg_homog hS h]
      exact lt_of_le_of_ne' hnm heq.symm
    · simp [Ideal.span_eq_bot.mpr hS]

theorem homogSubI_span_eq {n : ℕ} {S : Set (MvPolynomial α R)} {f : ℕ → Set (MvPolynomial α R)}
    (hS : S = f n) (hf : ∀ i ≥ n, f i ⊆ homogeneousSubmodule α R i) (hfz : ∀ i < n, f i ⊆ {0}) :
    homogeneousSubmoduleI n (Ideal.span S) = homogeneousSubmoduleI n (Ideal.span (⋃ i, f i)) := by
  rw [Ideal.span_iUnion, homogSubI_iSup]
  · have hss : ∀ i, homogeneousSubmoduleI n (Ideal.span (f i)) =
        if n = i then homogeneousSubmoduleI i (Ideal.span (f i)) else 0 := by
      intro i
      by_cases! hin : i ≥ n
      · exact homogSubI_span_apply hin (hf i hin)
      · simp [hin.ne.symm, Ideal.span_eq_bot.mpr (hfz i hin)]
    simp_rw [hss, iSup_ite, Submodule.zero_eq_bot, iSup_bot, sup_of_le_left bot_le,
      iSup_iSup_eq_right, hS]
  · intro i
    by_cases! hin : i < n
    · rw [Ideal.span_eq_bot.mpr (hfz i hin)]
      exact Ideal.IsHomogeneous.bot _
    · specialize hf i hin
      refine isHomogeneous_of_isSingleDegGen ?_
      rw [isSingleDegGen_iff]
      use i, f i

theorem minDeg_homog' {S : Set (MvPolynomial α R)}
    (h : ∀ f ∈ S, ∃ n : ℕ, f.IsHomogeneous n) (h0 : 0 ∉ S) :
    minDeg (Ideal.span S) = sInf (lowestDegree '' S) := by
  have hI : (Ideal.span S).IsHomogeneous (homogeneousSubmodule α R) := Ideal.homogeneous_span _ _ h
  by_cases! hb : Ideal.span S = ⊥
  · simp at hb
    have hS : S = ∅ := by grind
    simp [hS]
  refine le_antisymm ?_ ?_
  · refine Nat.sInf_le ?_
    simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
      Submodule.restrictScalars_mem, and_imp, not_forall, exists_prop, Set.mem_setOf_eq]
    obtain ⟨g, hgS, hg⟩ : ∃ g ∈ S, lowestDegree g = sInf (lowestDegree '' S) := by
      change sInf (lowestDegree '' S) ∈ lowestDegree '' S
      refine Nat.sInf_mem ?_
      rw [Set.image_nonempty]
      contrapose! hb
      simp [hb]
    use g
    have hg0 : g ≠ 0 := by grind
    constructor
    · rw [← hg]
      obtain ⟨n, hn⟩ := h g hgS
      rwa [lowestDegree_of_isHomogeneous hn hg0]
    constructor
    · exact Submodule.mem_span_of_mem hgS
    · exact hg0
  · obtain ⟨f, hf, hf0, hfh⟩ := nonzero_homog_of_ne_bot hb hI
    rw [Submodule.mem_span_iff_exists_finset_subset] at hf
    obtain ⟨φ, t, ht, hφt, hf⟩ := hf
    apply_fun (homogeneousComponent (minDeg (Ideal.span S))) at hf
    rw [homogeneousComponent_eq_self hfh, map_sum] at hf
    rw [← hf] at hf0
    obtain ⟨g, hgt, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf0
    apply ht at hgt
    obtain ⟨n, hn⟩ := h g hgt
    trans n
    · refine Nat.sInf_le ?_
      rw [Set.mem_image]
      use g
      simp [hgt, lowestDegree_of_isHomogeneous hn (by grind)]
    · simp only [smul_eq_mul, homogeneousComponent_mul, ne_eq] at hg
      apply Finset.exists_ne_zero_of_sum_ne_zero at hg
      obtain ⟨k, hk, hg⟩ := hg
      simp [homogeneousComponent_of_mem hn] at hg
      simp only [Finset.mem_antidiagonal, hg.1] at hk
      rw [← hk]
      exact Nat.le_add_left n k.1

theorem homogComps_gen_singleDegGen_ideal {I : Ideal (MvPolynomial α R)}
    {S : Set (MvPolynomial α R)} (h : IsSingleDegGen I) (hspan : I = Ideal.span S) :
    homogeneousSubmoduleI (minDeg I) I ≤ homogeneousSubmoduleI (minDeg I)
    (Ideal.span ((homogeneousComponent (minDeg I)) '' S)) := by
  have hI := isHomogeneous_of_isSingleDegGen h
  conv => lhs; rhs; rw [span_union_homogeneousComponent_image hspan hI]
  rw [← homogSubI_span_eq (n := (minDeg I)) (by rfl)]
  · intro i hi f
    simp only [Set.mem_image, SetLike.mem_coe, mem_homogeneousSubmodule, forall_exists_index,
      and_imp]
    intro g hg hf
    subst hf
    exact homogeneousComponent_isHomogeneous _ _
  · simp only [Set.subset_singleton_iff, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro i hi f hf
    have hif : homogeneousComponent i f ∈ I := by
      subst hspan
      exact homogeneousComponent_mem_of_mem hI (Submodule.mem_span_of_mem hf) _
    contrapose! hi
    refine Nat.sInf_le ?_
    simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
      Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq]
    use homogeneousComponent i f
    simp [hi, hif, homogeneousComponent_isHomogeneous]

theorem homogComps_gen_singleDegGen_ideal_finset [DecidableEq (MvPolynomial α R)]
    {I : Ideal (MvPolynomial α R)}
    {S : Finset (MvPolynomial α R)} (h : IsSingleDegGen I) (hspan : I = Ideal.span S) :
    homogeneousSubmoduleI (minDeg I) I ≤ homogeneousSubmoduleI (minDeg I)
    (Ideal.span (SetLike.coe (Finset.image (homogeneousComponent (minDeg I)) S))) := by
  simp only [Finset.coe_image]
  exact homogComps_gen_singleDegGen_ideal h hspan


theorem isSingleDegGen_iff_exists_finset [Finite α]
    {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal (MvPolynomial α R)} :
    IsSingleDegGen I ↔ ∃ S : Finset (MvPolynomial α R),
    SetLike.coe S ⊆ (homogeneousSubmodule α R (minDeg I)) ∧ I = Ideal.span S := by
  classical
  constructor
  · intro h
    obtain ⟨T, hI⟩ := ((isNoetherianRing_iff_ideal_fg (MvPolynomial α R)).mp isNoetherianRing) I
    use Finset.image (homogeneousComponent (minDeg I)) T
    have h₂ : SetLike.coe (Finset.image (homogeneousComponent (minDeg I)) T) ⊆
        homogeneousSubmodule α R (minDeg I) := by
      intro p
      simp only [Finset.coe_image, Set.mem_image, SetLike.mem_coe,
        mem_homogeneousSubmodule, forall_exists_index, and_imp]
      intro q hq hqp
      rw [← hqp]
      exact homogeneousComponent_isHomogeneous (minDeg I) q
    constructor
    · exact h₂
    nth_rw 1 [h]
    refine Submodule.span_eq_span ?_ ?_
    · intro p hp
      symm at hI
      apply homogComps_gen_singleDegGen_ideal h hI at hp
      rw [homogeneousSubmoduleI, Submodule.mem_inf, Submodule.restrictScalars_mem] at hp
      simp only [Finset.coe_image, SetLike.mem_coe]
      exact hp.2
    · refine subset_trans ?_ Submodule.subset_span
      intro p hp
      simp only [Submodule.coe_inf, Submodule.coe_restrictScalars, Set.mem_inter_iff,
        SetLike.mem_coe, mem_homogeneousSubmodule]
      constructor
      · exact h₂ hp
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
      obtain ⟨q, hq, hp⟩ := hp
      rw [← hp]
      refine homogeneousComponent_mem_of_mem (isHomogeneous_of_isSingleDegGen h) ?_ _
      rw [← hI]
      exact Submodule.mem_span_of_mem hq
  · intro h
    rw [isSingleDegGen_iff']
    obtain ⟨S, hS⟩ := h
    use SetLike.coe S

lemma isSingleDegGen_mul {I J : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I)
    (hJ : IsSingleDegGen J) : IsSingleDegGen (I * J) := by
  rw [isSingleDegGen_iff] at hI hJ
  obtain ⟨n, S, hI⟩ := hI
  obtain ⟨m, T, hJ⟩ := hJ
  rw [isSingleDegGen_iff]
  use n + m, S * T
  constructor
  · refine le_trans ?_ (homogeneousSubmodule_mul n m)
    refine le_trans (mul_le_mul' hI.1 hJ.1) ?_
    simp [Submodule.mul_def]
  · rw [hI.2, hJ.2]
    exact Ideal.span_mul_span _ _

lemma isSingleDegGen_pow {I : Ideal (MvPolynomial α R)} (h : IsSingleDegGen I) (n : ℕ) :
    IsSingleDegGen (I ^ n) := by
  induction n
  · simp
  · rename_i n ih
    rw [pow_succ]
    exact isSingleDegGen_mul ih h

@[simp]
lemma SetLike.mem_homogeneousSubmonoid {ι R S : Type*} [SetLike S R] [AddMonoid ι] [Monoid R]
    (A : ι → S) [SetLike.GradedMonoid A] {x : R} :
    x ∈ SetLike.homogeneousSubmonoid A ↔ SetLike.IsHomogeneousElem A x := by
  simp [SetLike.homogeneousSubmonoid]

@[simp]
lemma isHomogeneousElem_homogeneousSubmodule {α R : Type*} [CommSemiring R] {x : MvPolynomial α R} :
    SetLike.IsHomogeneousElem (homogeneousSubmodule α R) x ↔ ∃ n, x.IsHomogeneous n := by
  simp [SetLike.IsHomogeneousElem]

lemma minDeg_mul_eq_add_minDeg [NoZeroDivisors R]
    {I J : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I)
    (hJ : IsSingleDegGen J) (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) :
    minDeg (I * J) = minDeg I + minDeg J := by
  rw [isSingleDegGen_iff'] at hI hJ
  obtain ⟨S, hI⟩ := hI
  obtain ⟨T, hJ⟩ := hJ
  have hIJ : S * T ⊆ homogeneousSubmodule α R (minDeg I + minDeg J) := by
    refine le_trans ?_ (homogeneousSubmodule_mul _ _)
    refine le_trans (mul_le_mul' hI.1 hJ.1) ?_
    simp [Submodule.mul_def]
  have hIJ' : I * J = Ideal.span (S * T) := by
    rw [hI.2, hJ.2]
    exact Ideal.span_mul_span _ _
  rw [hIJ']
  refine minDeg_homog ?_ hIJ
  have hIJB : I * J ≠ ⊥ := mul_ne_zero hIB hJB
  rw [hIJ'] at hIJB
  contrapose! hIJB
  exact Ideal.span_eq_bot.mpr hIJB
