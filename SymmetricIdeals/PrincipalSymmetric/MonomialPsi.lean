/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.PrincipalSymmetric.PsiObstructions

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}
attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial Rename Equiv

lemma span_orderTypeComponent_le_symmSpan {p : MvPolynomial α R} {a : Multiset ℕ}
    (ha : a ∈ orderTypes p)
    (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : R)) '' S)) :
    Ideal.span (orderTypeComponent α R a) ≤ symmSpan {p} := by
  classical
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at ha
  obtain ⟨d, hd0, hda⟩ := ha
  suffices (monomial d (1 : R)) ∈ symmSpan {p} by
    apply symmSpan_singleton_le_of_mem at this
    rwa [symmSpan_monomial_eq_span_orderTypeComponent, hda] at this
  obtain ⟨S, hm⟩ := hm
  have hp : p ∈ symmSpan {p} := mem_symmSpan_self
  rw [hm, mem_ideal_span_monomial_image] at hp
  rw [← ne_eq, ← mem_support_iff] at hd0
  simp [hm, mem_ideal_span_monomial_image, hp d hd0]

lemma symmSpan_eq_span_orderTypeComponent {p : MvPolynomial α R} {a : Multiset ℕ}
    (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : R)) '' S))
    (hp : p.IsStronglyHomogeneous a) (hp0 : p ≠ 0) :
    symmSpan {p} = Ideal.span (orderTypeComponent α R a) := by
  refine le_antisymm (symmSpan_le_span_orderTypeComponent hp) ?_
  refine span_orderTypeComponent_le_symmSpan ?_ hm
  simp [(orderTypes_singleton_iff_isStronglyHomogeneous hp0).mpr hp]

lemma le_symmSpan_of_le_sup_symmSpan {S : Finset (Multiset ℕ)} {a : S} {g : S → MvPolynomial α R}
    (hdis : ∀ a b : S, a ≠ b → Disjoint (orderTypes (g a)) (orderTypes (g b)))
    (hag : orderTypes (g a) = {a.1}) (hgh : ∀ b, (g b).IsHomogeneous (a.1.sum))
    (h : Ideal.span (orderTypeComponent α R a) ≤ ⨆ b, symmSpan {g b}) :
    Ideal.span (orderTypeComponent α R a) ≤ symmSpan {g a} := by
  rw [Ideal.span_le]
  intro p hp
  by_cases! hp0 : p = 0
  · simp [hp0, symmSpan]
  have hpsh := hp
  simp only [SetLike.mem_coe, mem_orderTypeComponent_iff] at hpsh
  apply Ideal.subset_span at hp
  apply h at hp
  have hp : p ∈ ⨆ b, Submodule.span R (symmSet {g b}) := by
    have hb : ∀ b, Submodule.span R (symmSet {g b}) =
        homogeneousSubmoduleI a.1.sum (Ideal.span (symmSet {g b})) := by
      intro b
      exact (homogSubI_span _ _ <| symmSet_subset_homogSub_of_isHomogeneous (hgh b)).symm
    simp_rw [hb]
    rw [← homogSubI_iSup, homogeneousSubmoduleI, Submodule.mem_inf, mem_homogeneousSubmodule]
    constructor
    · exact isHomogeneous_of_isStronglyHomogeneous a hpsh
    · rwa [Submodule.restrictScalars_mem]
    intro b
    exact isHomogeneous_of_isSingleDegGen (isSingleDegGen_symmSpan (hgh b))
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hp
  obtain ⟨φ, hφ, hp⟩ := hp
  suffices ∀ i : S, i ≠ a → φ i = 0 by
    rw [← hp, Finsupp.sum_eq_single a]
    · exact Submodule.span_subset_span R _ _ (hφ a)
    · grind
    · simp
  intro i hia
  by_cases! his : i ∉ φ.support
  · simpa using his
  suffices orderTypes (φ i) ⊆ (orderTypes p) ∩ (orderTypes (g i))  by
    simpa [(orderTypes_singleton_iff_isStronglyHomogeneous hp0).mpr hpsh,
      ← hag, Finset.disjoint_iff_inter_eq_empty.mp (hdis a i hia.symm)] using this
  have hjg : ∀ j : S, orderTypes (φ j) ⊆ orderTypes (g j) := by
    intro j
    obtain ⟨f, t, ht, hf, hφj⟩ := Submodule.mem_span_iff_exists_finset_subset.mp (hφ j)
    rw [← hφj]
    refine subset_trans orderTypes_sum_subset ?_
    simp only [Finset.biUnion_subset_iff_forall_subset]
    intro d hd
    refine subset_trans orderTypes_smul ?_
    apply ht at hd
    rw [mem_symmSet_singleton] at hd
    obtain ⟨σ, hd⟩ := hd
    rw [← hd, orderTypes_perm]
  simp only [← hp, Finsupp.sum, Finset.subset_inter_iff, hjg i, and_true]
  rw [orderTypes_sum]
  · exact Finset.subset_biUnion_of_mem (fun x ↦ orderTypes (φ x)) his
  · exact fun x y _ _ hxy ↦ Disjoint.mono (hjg x) (hjg y) <| hdis x y hxy

lemma mem_orderTypes_isHomogeneous {p : MvPolynomial α R} {n : ℕ} {a : Multiset ℕ}
    (hp : p.IsHomogeneous n) (ha : a ∈ orderTypes p) : n = a.sum := by
  obtain ⟨d, hd, hda⟩ := Finset.mem_image.mp ha
  simp [← hda, orderType_sum_eq_degree, ← hp (mem_support_iff.mp hd),
    Finsupp.degree_eq_weight_one, Finsupp.weight_apply]

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {I : Ideal (MvPolynomial α R)}

theorem isStronglyHomogeneous_of_monomial_ideal {p : MvPolynomial α R} (n : ℕ)
    (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : R)) '' S))
    (hp : p.IsHomogeneous n) : ∃ a : Multiset ℕ, IsStronglyHomogeneous p a := by
  classical
  by_cases hp0 : p = 0
  · use 0
    simp [hp0]
  let g : (orderTypes p) → MvPolynomial α R :=
    fun a => ∑ d ∈ p.support with orderType d = a, monomial d (coeff d p)
  have hgp : p = ∑ a, g a := by
    simp only [Finset.univ_eq_attach, Finset.sum_filter, g]
    nth_rw 1 [Finset.sum_comm, as_sum p]
    refine Finset.sum_congr rfl ?_
    intro d hd'
    symm
    have hd : orderType d ∈ orderTypes p := by
      rw [mem_support_iff] at hd'
      exact mem_orderTypes_of_coeff_ne_zero hd'
    nth_rw 2 [show monomial d (coeff d p) = if orderType d =
      (⟨orderType d, hd⟩ : orderTypes p).1 then monomial d (coeff d p) else 0 by simp]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (by grind)
  have hgsh : ∀ a, IsStronglyHomogeneous (g a) a := by
    intro a d hd
    simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, mem_support_iff,
      ne_eq, ite_eq_right_iff, and_imp, Classical.not_imp, g] at hd
    exact hd.2.1
  have hmdp : ∀ a ∈ orderTypes p, minDeg (symmSpan {p}) = a.sum := by
    intro a ha
    rw [minDeg_symmSpan hp hp0]
    exact mem_orderTypes_isHomogeneous hp ha
  have hgh : ∀ a, (g a).IsHomogeneous (minDeg (symmSpan {p})) := by
    intro a
    rw [hmdp a a.2]
    exact isHomogeneous_of_isStronglyHomogeneous a (hgsh a)
  have hgz : ∀ a, g a ≠ 0 := by
    intro ⟨a, ha⟩
    rw [ne_zero_iff]
    simp only [Finset.mem_image, mem_support_iff, ne_eq] at ha
    obtain ⟨d, hd⟩ := ha
    use d
    simp [g, coeff_sum, hd]
  have hgd : ∀ a b, a ≠ b → Disjoint (orderTypes (g a)) (orderTypes (g b)) := by
    intro a b hab
    rw [(orderTypes_singleton_iff_isStronglyHomogeneous (hgz a)).mpr (hgsh a)]
    rw [(orderTypes_singleton_iff_isStronglyHomogeneous (hgz b)).mpr (hgsh b)]
    simpa
  have hgi : ∀ a, g a ∈ symmSpan {p} := by
    intro a
    unfold g
    refine Submodule.sum_mem _ ?_
    simp only [Finset.mem_filter, and_imp]
    intro d hd hda
    suffices monomial d 1 ∈ Ideal.span (symmSet {p}) by
      apply Submodule.smul_mem _ (C (coeff d p)) at this
      simpa [C_mul_monomial] using this
    obtain ⟨T, hT⟩ := hm
    unfold symmSpan at hT
    rw [hT]
    have hpI : p ∈ symmSpan {p} := mem_symmSpan_self
    rw [symmSpan, hT, mem_ideal_span_monomial_image] at hpI
    simp [mem_ideal_span_monomial_image, hpI d hd]
  have hgot : ∀ a, symmSpan {g a} = Ideal.span (orderTypeComponent α R a) := by
    intro a
    apply span_orderTypeComponent_le_symmSpan a.2 at hm
    simp_rw [hgp] at hm
    apply le_trans' symmSpan_sum_le_sup_symmSpan at hm
    apply le_symmSpan_of_le_sup_symmSpan hgd at hm
    · exact le_antisymm (symmSpan_le_span_orderTypeComponent <| hgsh a) hm
    · rw [orderTypes_singleton_iff_isStronglyHomogeneous (hgz a)]
      exact hgsh a
    · rwa [← hmdp a.1 a.2]
  have hgeo : ∀ a, evalOne (g a) ≠ 0 := by
    intro a
    specialize hgot a
    contrapose! hgot
    exact (symmSpan_lt_span_orderTypeComponent (hgsh a) (hgz a) hgot).ne
  suffices (orderTypes p).card ≤ 1 by
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rcases this with h0 | h1
    · simp [hp0] at h0
    · obtain ⟨a, h1⟩ := Finset.card_eq_one.mp h1
      use a
      rwa [← orderTypes_singleton_iff_isStronglyHomogeneous hp0]
  by_contra! hS
  rw [← Fintype.card_coe, Fintype.one_lt_card_iff] at hS
  obtain ⟨a, b, hab⟩ := hS
  suffices ¬IsPrincipalSymmetric (symmSpan {p}) by apply this; use p
  exact not_psi_of_nonzero_disjoint_orderTypes (isSingleDegGen_symmSpan hp) (hgh a) (hgh b) (hgeo a)
    (hgeo b) (hgd a b hab) (hgi a) (hgi b)

theorem monomial_iff_symmSpan_monomial (h : IsPrincipalSymmetric I) (hI : IsSingleDegGen I)
    (hIB : I ≠ ⊥) : (∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : R)) '' S)) ↔
    ∃ d : α →₀ ℕ, I = symmSpan {monomial d (1 : R)} := by
  constructor
  · intro hm
    obtain ⟨p, hph, hp⟩ := exists_homog_gen_of_psi_isSingleDegGen hI h
    rw [hp] at hm
    have hp0 : p ≠ 0 := by
      contrapose! hIB
      simp [hp, hIB]
    apply isStronglyHomogeneous_of_monomial_ideal (minDeg I) hm at hph
    obtain ⟨a, hsh⟩ := hph
    rw [hp, symmSpan_eq_span_orderTypeComponent hm hsh hp0]
    obtain ⟨d, hd⟩ := exists_symmSpan_monomial_eq_span_orderTypeComponent hp0 hsh
    use d
    exact hd.symm
  · intro ⟨d, hd⟩
    use Set.range (fun σ : Perm α ↦ Finsupp.mapDomain σ d)
    rw [hd, symmSpan, symmSet_singleton_eq_range]
    congr
    ext f
    simp
