/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Upstream

open MvPolynomial

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

attribute [local instance] MvPolynomial.gradedAlgebra


lemma homogeneousComponent_eq_self {f : MvPolynomial α R} {n : ℕ} (hf : f.IsHomogeneous n) :
    homogeneousComponent n f = f := by
  simp [homogeneousComponent_of_mem hf]


noncomputable
abbrev homogeneousSubmoduleI (n : ℕ) (I : Ideal (MvPolynomial α R)) :
  Submodule R (MvPolynomial α R) := (homogeneousSubmodule α R n) ⊓ (Submodule.restrictScalars R I)

lemma homogSubI_monotone (n : ℕ) {I J : Ideal (MvPolynomial α R)} (h : I ≤ J) :
    homogeneousSubmoduleI n I ≤ homogeneousSubmoduleI n J := inf_le_inf_left _ h

@[simp]
lemma homogeneousSubmoduleI_zero {n : ℕ} :
    homogeneousSubmoduleI n (0 : Ideal (MvPolynomial α R)) = 0 := by
  simp only [Submodule.zero_eq_bot, Submodule.restrictScalars_bot, bot_le, inf_of_le_right]

open Classical in
lemma coeff_mul_single_homog {d : α →₀ ℕ} {n : ℕ}
    {f g : MvPolynomial α R} (hd : d.degree = n) (hg : g.IsHomogeneous n) :
    coeff d (f * g) = coeff 0 f * coeff d g := by
  rw [coeff_mul]
  refine Finset.sum_eq_single_of_mem (0, d) ?_ (fun b hab hbd ↦ ?_)
  · rw [Finset.mem_antidiagonal, zero_add]
  rw [Finset.mem_antidiagonal] at hab
  have hb2 : b.2.degree ≠ n := by grind [Finsupp.degree_eq_zero_iff]
  simp [hg.coeff_eq_zero hb2]

lemma span_le_homogSub_iff {S : Set (MvPolynomial α R)} {n : ℕ} :
    Submodule.span R S ≤ homogeneousSubmodule α R n ↔ S ≤ homogeneousSubmodule α R n := by
  refine ⟨le_trans Submodule.subset_span, fun h ↦ ?_⟩
  rw [← Submodule.span_eq (homogeneousSubmodule α R n)]
  exact Submodule.span_monotone h

lemma homogeneousComponent_mul {f g : MvPolynomial α R} {n : ℕ} :
    homogeneousComponent n (f * g) = ∑ d ∈ Finset.antidiagonal n,
    homogeneousComponent d.1 f * homogeneousComponent d.2 g := by
  ext c
  classical simp only [coeff_homogeneousComponent, coeff_mul, coeff_sum, mul_ite, ite_mul, zero_mul,
    mul_zero]
  split_ifs with h
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp at hx
    rw [Finset.sum_eq_single_of_mem (x.1.degree, x.2.degree)]
    · simp
    · simp [← h, ← map_add, hx]
    · grind
  · symm
    refine Finset.sum_eq_zero ?_
    intro b hb
    refine Finset.sum_eq_zero ?_
    simp_all
    grind

lemma exists_homog_finset_subset_of_mem {s : Set (MvPolynomial α R)} {f : MvPolynomial α R} {n : ℕ}
    (hs : s ≤ homogeneousSubmodule α R n) (hf : f.IsHomogeneous n)
    (h : f ∈ Ideal.span s) : ∃ φ : MvPolynomial α R → R, ∃ t : Finset (MvPolynomial α R),
    ↑t ⊆ s ∧ Function.support φ ⊆ ↑t ∧ ∑ a ∈ t, φ a • a = f := by
  rw [Submodule.mem_span_iff_exists_finset_subset] at h
  obtain ⟨ψ, t, ht, hψt, hft⟩ := h
  use (fun a ↦ coeff 0 (ψ a)), t, ht
  constructor
  · intro x hx
    apply hψt
    simp only [Function.mem_support] at hx ⊢
    rw [← support_nonempty]
    use 0
    simp [hx]
  · rw [← homogeneousComponent_eq_self hf, ← hft]
    simp only [smul_eq_mul, map_sum, homogeneousComponent_mul]
    refine Finset.sum_congr rfl ?_
    intro a hat
    rw [smul_eq_C_mul, ← homogeneousComponent_zero]
    apply ht at hat
    apply hs at hat
    conv => lhs; rhs; rw [← homogeneousComponent_eq_self hat]
    symm
    refine Finset.sum_eq_single_of_mem (0, n) (by simp) ?_
    intro d hd hd0
    simp at hd
    suffices d.2 ≠ n by simp [homogeneousComponent_of_mem hat, this]
    grind

open Classical in
@[simp]
theorem homogSubI_span (n : ℕ) (S : Set (MvPolynomial α R))
    (h : S ⊆ (homogeneousSubmodule α R n)) :
    homogeneousSubmoduleI n (Ideal.span S) = Submodule.span R S := by
  refine le_antisymm ?_ ?_
  · intro p hp
    obtain ⟨hpm, hp⟩ := Submodule.mem_inf.mp hp
    rw [mem_homogeneousSubmodule] at hpm
    rw [Submodule.restrictScalars_mem R (Ideal.span S) p] at hp
    obtain ⟨φ, t, hts, hφt, hpt⟩ := exists_homog_finset_subset_of_mem h hpm hp
    rw [Submodule.mem_span_iff_exists_finset_subset]
    use φ, t
  · simp [le_inf_iff, span_le_homogSub_iff, h, Submodule.span_le_restrictScalars]

lemma homogSubI_iSup {ι : Type*} {n : ℕ} {f : ι → Ideal (MvPolynomial α R)}
    (hh : ∀ i, (f i).IsHomogeneous (homogeneousSubmodule α R)) :
    homogeneousSubmoduleI n (⨆ i, f i) = ⨆ i, (homogeneousSubmoduleI n (f i)) := by
  simp_rw [homogeneousSubmoduleI, Submodule.restrictScalars_iSup]
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [Submodule.mem_inf] at hp
    obtain ⟨a, hf, hpf⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hp.2
    rw [Submodule.mem_iSup_iff_exists_finsupp]
    simp only [Submodule.restrictScalars_mem] at hf
    use Finsupp.mapRange (homogeneousComponent n) (map_zero _) a
    constructor
    · intro i
      simp [homogeneousComponent_isHomogeneous, homogeneousComponent_mem_of_mem (hh i) (hf i)]
    · rw [← homogeneousComponent_eq_self hp.1, ← hpf,
        Finsupp.sum_mapRange_index, map_finsuppSum]
      simp
  · exact iSup_inf_le_inf_iSup _ _



noncomputable
def minDeg (I : Ideal (MvPolynomial α R)) := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}

@[simp]
lemma minDeg_bot : minDeg (⊥ : Ideal (MvPolynomial α R)) = 0 := by
  simp [minDeg]

@[simp]
lemma minDeg_top : minDeg (⊤ : Ideal (MvPolynomial α R)) = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp [Submodule.eq_bot_of_subsingleton]
  · simp [minDeg, ← Submodule.zero_eq_bot]

lemma minDeg_mem (h : minDeg I ≠ 0) : minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  refine Nat.sInf_mem ?_
  contrapose! h
  simp [minDeg, h]

lemma bot_of_empty_minDeg (h : I.IsHomogeneous (homogeneousSubmodule α R))
    (hIB : {n | homogeneousSubmoduleI n I ≠ ⊥} = ∅) : I = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [← sum_homogeneousComponent p]
  refine Finset.sum_eq_zero ?_
  intro i _
  contrapose! hIB
  use i
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq]
  use homogeneousComponent i p
  simp [hIB, homogeneousComponent_isHomogeneous, homogeneousComponent_mem_of_mem h hp]

lemma minDeg_mem' (h : I ≠ ⊥) (hI : I.IsHomogeneous (homogeneousSubmodule α R)) :
    minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  refine Nat.sInf_mem ?_
  contrapose! h
  exact bot_of_empty_minDeg hI h

lemma nonzero_homog_of_ne_bot (h : I ≠ ⊥) (hI : I.IsHomogeneous (homogeneousSubmodule α R)) :
    ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  obtain ⟨p, h⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <| minDeg_mem' h hI
  simp at h
  use p
  tauto

lemma nonzero_homog_of_minDeg_nonzero (h : minDeg I ≠ 0) :
    ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  obtain ⟨p, h⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <| minDeg_mem h
  simp at h
  use p
  tauto

theorem minDeg_antitone {J : Ideal (MvPolynomial α R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule α R)) (hb : I ≠ ⊥) (hIJ : I ≤ J) :
    minDeg I ≥ minDeg J := by
  refine Nat.sInf_le ?_
  simp only [ne_eq, ← bot_lt_iff_ne_bot, Set.mem_setOf_eq]
  refine lt_of_lt_of_le ?_ (homogSubI_monotone _ hIJ)
  rw [bot_lt_iff_ne_bot]
  exact minDeg_mem' hb hI

@[simp]
theorem minDeg_homog {n : ℕ} {S : Set (MvPolynomial α R)} (hS : ∃ p ∈ S, p ≠ 0)
    (h : S ⊆ homogeneousSubmodule α R n) : minDeg (Ideal.span S) = n := by
  have hn : n ∈ {n | homogeneousSubmoduleI n (Ideal.span S) ≠ ⊥} := by
    simp [homogSubI_span n S h, Submodule.span_eq_bot, hS]
  refine le_antisymm (Nat.sInf_le hn) ?_
  refine le_csInf (by use n) ?_
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq, forall_exists_index]
  intro m p hp hpS hp0
  by_contra! hnm
  rw [Submodule.mem_span_iff_exists_finset_subset] at hpS
  obtain ⟨f, T, hTS, hfT, hps⟩ := hpS
  suffices ∀ i ∈ Finset.range (p.totalDegree + 1), (homogeneousComponent i p) = 0 by
    rw [← sum_homogeneousComponent p] at hp0
    apply Finset.sum_eq_zero at this
    contradiction
  intro i hi
  rw [IsHomogeneous.totalDegree hp hp0, Finset.mem_range] at hi
  apply Nat.lt_of_lt_of_le hi at hnm
  simp only [← hps, smul_eq_mul, map_sum]
  refine Finset.sum_eq_zero ?_
  intro x hxT
  rw [homogeneousComponent_mul]
  refine Finset.sum_eq_zero ?_
  intro a ha
  refine mul_eq_zero_of_right _ ?_
  apply hTS at hxT
  apply h at hxT
  simp [homogeneousComponent_of_mem hxT]
  grind [Finset.mem_antidiagonal]

section Field

variable {R : Type*} [Field R] {I : Ideal (MvPolynomial α R)}

lemma top_of_zero_mem_minDeg (h : 0 ∈ {n | homogeneousSubmoduleI n I ≠ ⊥}) : I = ⊤ := by
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq] at h
  obtain ⟨p, hph, hp, hp0⟩ := h
  refine Ideal.eq_top_of_isUnit_mem _ hp ?_
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hph
  rw [hph, C_eq_zero] at hp0
  rw [hph]
  exact IsUnit.map C <| Ne.isUnit hp0

lemma minDeg_zero_iff (h : I.IsHomogeneous (homogeneousSubmodule α R)) :
    minDeg I = 0 ↔ I = ⊤ ∨ I = ⊥ := by
  constructor
  · rw [minDeg, Nat.sInf_eq_zero]
    intro hI
    rcases hI with hIT | hIB
    · left; exact top_of_zero_mem_minDeg hIT
    · right; exact bot_of_empty_minDeg h hIB
  · grind [minDeg_top, minDeg_bot]

lemma zero_of_minDeg_zero (hh : I.IsHomogeneous (homogeneousSubmodule α R)) (hIT : I ≠ ⊤)
    (h : minDeg I = 0) : I = 0 := by
  rw [Submodule.zero_eq_bot]
  rw [minDeg_zero_iff hh] at h
  tauto

end Field
