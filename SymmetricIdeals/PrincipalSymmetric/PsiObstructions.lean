/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Homogeneous.GradedMinimalGenerators
import SymmetricIdeals.Symmetry.Basic
import SymmetricIdeals.Symmetry.Homogeneous
import SymmetricIdeals.PrincipalSymmetric.OrderType

open MvPolynomial Rename Equiv

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

abbrev evalOne : MvPolynomial α R →+* R := eval (fun _ => (1 : R))

@[simp]
lemma evalOne_monomial (d : α →₀ ℕ) (c : R) : evalOne (monomial d c) = c := by
  simp [eval]

lemma evalOne_monomial_ne_zero [Nontrivial R] (d : α →₀ ℕ) : evalOne (monomial d (1 : R)) ≠ 0 := by
  simp

@[simp]
lemma evalOne_perm {p : MvPolynomial α R} (σ : Equiv.Perm α) : evalOne (σ • p) = evalOne p := by
  simp [evalOne, symmAct_def, eval_rename]
  rfl

@[simp]
lemma evalOne_smul {p : MvPolynomial α R} {c : R} : evalOne (c • p) = c * evalOne p := by
  simp

lemma evalOne_eq_zero_of_mem_symmSpan {S : Set (MvPolynomial α R)} (h : ∀ q ∈ S, evalOne q = 0)
    {p : MvPolynomial α R} (hp : p ∈ symmSpan S) : evalOne p = 0 := by
  rw [symmSpan, symmSet, Ideal.mem_span] at hp
  refine hp (RingHom.ker evalOne) ?_
  intro f
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, RingHom.mem_ker, forall_exists_index,
    and_imp]
  intro σ q hq hf
  subst hf
  rw [evalOne_perm σ, h q hq]

theorem symmSpan_lt_span_orderTypeComponent {p : MvPolynomial α R} {a : Multiset ℕ}
    (hp : p.IsStronglyHomogeneous a) (hp0 : p ≠ 0) (hp1 : evalOne p = 0) :
    symmSpan {p} < Ideal.span (SetLike.coe (orderTypeComponent α R a)) := by
  classical
  have hR : Nontrivial R := by
    contrapose! hp0
    exact Subsingleton.allEq _ _
  refine lt_of_le_of_ne ?_ ?_
  · exact symmSpan_le_span_orderTypeComponent hp
  rw [ne_zero_iff] at hp0
  obtain ⟨d, hd0⟩ := hp0
  suffices monomial d (1 : R) ∈ Ideal.span (orderTypeComponent α R a) ∧
      monomial d (1 : R) ∉ symmSpan {p} by
    obtain ⟨hmi, hms⟩ := this
    contrapose! hms
    rwa [hms]
  constructor
  · refine Submodule.mem_span_of_mem ?_
    simp [orderTypeComponent, IsStronglyHomogeneous, hp hd0]
  contrapose! hd0
  apply evalOne_eq_zero_of_mem_symmSpan at hd0
  · simp at hd0
  simp [hp1]

lemma minDeg_stronglyHomogeneous_symmSpan {p : MvPolynomial α R} {a : Multiset ℕ}
    (hp : p.IsStronglyHomogeneous a) (hp0 : p ≠ 0) :
    minDeg (symmSpan {p}) = minDeg (Ideal.span (SetLike.coe (orderTypeComponent α R a))) := by
  rw [minDeg_symmSpan (isHomogeneous_of_isStronglyHomogeneous _ hp) hp0,
    minDeg_orderTypeComponent (by use p; constructor <;> assumption)]

lemma mem_span_symmSet_of_homog {n : ℕ} {f p : MvPolynomial α R} (hf : f.IsHomogeneous n)
    (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) : p ∈ Submodule.span R (symmSet {f}) := by
  rw [← homogSubI_span n _ (symmSet_subset_homogSub_of_isHomogeneous hf), homogeneousSubmoduleI,
    Submodule.mem_inf, Submodule.restrictScalars_mem]
  tauto

lemma all_fin_of_lt_fin {r : ℕ} {p : Fin r → Fin r → Prop} (hsymm : ∀ i j : Fin r, p i j ↔ p j i)
    (h : ∀ i j : Fin r, i < j → p i j) (i j : Fin r) (hij : i ≠ j) : p i j := by
  wlog! hlt : i < j
  · specialize this hsymm h j i hij.symm <| lt_of_le_of_ne hlt hij.symm
    rwa [hsymm]
  exact h i j hlt

lemma orderTypes_sum_subset' {φ : Equiv.Perm α →₀ R} {g : MvPolynomial α R} :
    orderTypes (∑ σ ∈ φ.support, (φ σ) • σ • g) ⊆ orderTypes g := by
  refine subset_trans orderTypes_sum_subset ?_
  simp only [Finset.biUnion_subset_iff_forall_subset, Finsupp.mem_support_iff, ne_eq]
  intro σ hσ
  refine subset_trans orderTypes_smul ?_
  simp

lemma orderTypes_sum_support_eq_orderTypes_finsupp_sum {f p : MvPolynomial α R}
    {c : Perm α →₀ R} (h : (c.sum (fun i a ↦ a • i • f)) = p) :
    orderTypes (∑ d : f.support with orderType d.1 ∈ orderTypes p, (monomial d.1) (coeff d f)) =
    orderTypes p := by
  classical
  ext s
  constructor
  · simp only [orderTypes, Finset.mem_image, mem_support_iff, coeff_sum, coeff_monomial, ne_eq,
      forall_exists_index, and_imp]
    intro d hd hs
    obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    simpa only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and,
      hx.1, hs] using hxS
  · intro hs
    simp only [Finset.mem_image, mem_support_iff, coeff_sum, coeff_monomial, ne_eq]
    have hs2 := hs
    simp only [Finset.mem_image, mem_support_iff, ne_eq] at hs2
    obtain ⟨d, hd, hds⟩ := hs2
    have hsf : s ∈ orderTypes f := by
      suffices orderTypes p ⊆ orderTypes f by exact this hs
      simp only [← h]
      exact orderTypes_sum_subset'
    simp only [Finset.mem_image, mem_support_iff, ne_eq] at hsf
    obtain ⟨e, he, hes⟩ := hsf
    use e
    constructor
    · rw [Finset.sum_eq_single ⟨e, mem_support_iff.mpr he⟩]
      · simpa
      · grind
      · simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and,
          not_exists, not_and, ↓reduceIte, he, imp_false, not_forall, Decidable.not_not]
        use d
        simp [hd, hes, hds]
    · exact hes

section CommRing

lemma evalOne_stronglyHomogeneous_decomposition [NoZeroDivisors R] {f p : MvPolynomial α R}
    {r n : ℕ} (g : Fin r → MvPolynomial α R) (hsum : f = ∑ i, g i)
    (hdot : ∀ i j : Fin r, i < j → Disjoint (orderTypes (g i)) (orderTypes (g j)))
    (hfh : f.IsHomogeneous n) (hph : p.IsHomogeneous n) (hpI : p ∈ symmSpan {f}) (i₀ : Fin r)
    (hg : ∀ i : Fin r, i ≠ i₀ → Disjoint (orderTypes (g i)) (orderTypes p)) (hp0 : evalOne p ≠ 0)
    (i : Fin r) (hi₀ : i ≠ i₀) : evalOne (g i) = 0 := by
  apply all_fin_of_lt_fin at hdot
  · have hc := mem_span_symmSet_of_homog hfh hph hpI
    rw [symmSet_singleton_eq_range, Finsupp.mem_span_range_iff_exists_finsupp] at hc
    obtain ⟨c, hc⟩ := hc
    simp only [Finsupp.sum, hsum, Finset.smul_sum] at hc
    rw [Finset.sum_comm] at hc
    symm at hc
    have hgi : ∀ i ≠ i₀, ∑ σ ∈ c.support, c σ • σ • g i = 0 := by
      refine eq_zero_of_disjoint_sum hc ?_ i₀ ?_
      · intro j j' hj
        exact Disjoint.mono orderTypes_sum_subset' orderTypes_sum_subset' <| hdot j j' hj
      · intro j hj
        exact Disjoint.mono_left orderTypes_sum_subset' <| hg j hj
    have hpi₀ : p = ∑ σ ∈ c.support, c σ • σ • g i₀ := by
      rw [hc]
      exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ i₀) (fun i _ hi ↦ hgi i hi)
    have hp1 : evalOne p = (evalOne (g i₀)) * (∑ σ ∈ c.support, c σ) := by
      simp_rw [hpi₀, map_sum, smul_eval, evalOne_perm, Finset.mul_sum, mul_comm]
    have hgi1 : (evalOne (g i)) * (∑ σ ∈ c.support, c σ) = 0 := by
      specialize hgi i hi₀
      apply_fun evalOne at hgi
      simp_rw [map_sum, smul_eval, evalOne_perm, map_zero, ← Finset.sum_mul] at hgi
      rwa [mul_comm]
    rw [hp1] at hp0
    apply right_ne_zero_of_mul at hp0
    exact (mul_eq_zero_iff_right hp0).mp hgi1
  · simp [disjoint_comm]

variable {R : Type*} [CommRing R]

lemma split_orderTypes {f p : MvPolynomial α R} {n : ℕ} (hf : f.IsHomogeneous n)
    (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) : ∃ p' q, f = p' + q ∧
    orderTypes p' = orderTypes p ∧ Disjoint (orderTypes p) (orderTypes q) ∧
    (evalOne p ≠ 0 → evalOne p' ≠ 0) := by
  classical
  have hfp := mem_span_symmSet_of_homog hf hp h
  rw [symmSet_singleton_eq_range, Finsupp.mem_span_range_iff_exists_finsupp] at hfp
  obtain ⟨c, hc⟩ := hfp
  let S := {d : f.support | orderType d.1 ∈ orderTypes p}
  have hfpq : f = (∑ d ∈ S, monomial d (coeff d f)) + (f - (∑ d ∈ S, monomial d (coeff d f))) := by
    ring
  use ∑ d ∈ S, monomial d (coeff d f), f - (∑ d ∈ S, monomial d (coeff d f))
  have hotp : orderTypes (∑ d ∈ S.toFinset, (monomial d.1) (coeff d f)) = orderTypes p := by
    simp only [Set.toFinset_setOf, S]
    exact orderTypes_sum_support_eq_orderTypes_finsupp_sum hc
  constructor
  · exact hfpq
  constructor
  · exact hotp
  have hpq : Disjoint (orderTypes p)
      (orderTypes (f - ∑ d ∈ S.toFinset, (monomial d.1) (coeff d f))) := by
    rw [← Finset.disjoint_coe, ← Set.subset_compl_iff_disjoint_right]
    intro s
    simp only [orderTypes, Finset.coe_image, Set.mem_image, SetLike.mem_coe, mem_support_iff, ne_eq,
      Set.mem_compl_iff, coeff_sub, not_exists, not_and, forall_exists_index, and_imp]
    intro d hdc hd e he
    contrapose! he
    rw [coeff_sum]
    by_cases! hef : e ∈ f.support
    · have hef2 : ⟨e, hef⟩ ∈ S := by
        unfold S
        rw [Set.mem_setOf, Subtype.coe_mk, he, ← hd]
        exact mem_orderTypes_of_coeff_ne_zero hdc
      rw [Finset.sum_eq_single ⟨e, hef⟩] <;> grind [coeff_monomial]
    · rw [notMem_support_iff] at hef
      rw [hef, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero ?_
      grind [coeff_monomial]
  constructor
  · exact hpq
  contrapose!
  intro hp0
  have hpsum : p = (∑ σ ∈ c.support, c σ • σ • (∑ d ∈ S.toFinset, (monomial d) (coeff d f))) +
      (∑ σ ∈ c.support, c σ • σ • (f - ∑ d ∈ S.toFinset, (monomial d) (coeff d f))) := by
    simp [← Finset.sum_add_distrib, ← smul_add, ← hc, Finsupp.sum]
  rw [hpsum]
  suffices ∑ σ ∈ c.support, c σ • σ • (f - ∑ d ∈ S.toFinset, (monomial d) (coeff d f)) = 0 by
    simp [this, add_zero, map_sum, evalOne_perm, hp0]
  refine eq_zero_of_disjoint_add hpsum (Disjoint.mono_right orderTypes_sum_subset' hpq) ?_
  refine Disjoint.mono orderTypes_sum_subset' orderTypes_sum_subset' ?_
  rwa [hotp]

theorem not_psi_of_nonzero_disjoint_orderTypes [NoZeroDivisors R]
    {I : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I) {p₁ p₂ : MvPolynomial α R}
    (hp₁ : p₁.IsHomogeneous (minDeg I)) (hp₂ : p₂.IsHomogeneous (minDeg I)) (hp₁z : evalOne p₁ ≠ 0)
    (hp₂z : evalOne p₂ ≠ 0) (h : Disjoint (orderTypes p₁) (orderTypes p₂))
    (hIp₁ : p₁ ∈ I) (hIp₂ : p₂ ∈ I) : ¬IsPrincipalSymmetric I := by
  by_contra! hpsi
  obtain ⟨f, hf, hpsi⟩ := exists_homog_gen_of_psi_isSingleDegGen hI hpsi
  rw [hpsi] at hIp₁ hIp₂
  obtain ⟨p₁', q₁, hs₁, hoe₁, hod₁, he₁⟩ := split_orderTypes hf hp₁ hIp₁
  obtain ⟨p₂', q₂, hs₂, hoe₂, hod₂, he₂⟩ := split_orderTypes hf hp₂ hIp₂
  have hp12 : Disjoint (orderTypes p₁') (orderTypes p₂') := by rwa [hoe₁, hoe₂]
  have hpq₁ : Disjoint (orderTypes p₁') (orderTypes q₁) := by rwa [hoe₁]
  have hpq₂ : Disjoint (orderTypes p₂') (orderTypes q₂) := by rwa [hoe₂]
  have hpqf₁ : orderTypes p₁' ⊆ orderTypes q₂ := by
    rw [hs₁] at hs₂
    exact orderTypes_subset_of_add_eq_add hp12 hpq₁ hpq₂ hs₂
  have hpqf₂ : orderTypes p₂' ⊆ orderTypes q₁ := by
    rw [hs₂] at hs₁
    rw [disjoint_comm] at hp12
    exact orderTypes_subset_of_add_eq_add hp12 hpq₂ hpq₁ hs₁
  have hpq1 : Disjoint (orderTypes p₁') (orderTypes (q₂ - p₁')) := by
    refine disjoint_sub_orderTypes_of_add_eq_add hp12 hpq₁ ?_
    rw [← hs₁, ← hs₂]
  have hpq2 : Disjoint (orderTypes p₂') (orderTypes (q₂ - p₁')) :=
    orderTypes_disjoint_sub hpq₂ hpqf₁
  have hpp1 : Disjoint (orderTypes p₂') (orderTypes p₁) := by
    refine Finset.disjoint_of_subset_left hpqf₂ ?_
    rwa [disjoint_comm]
  have hq2p : Disjoint (orderTypes (q₂ - p₁')) (orderTypes p₁) := by rwa [← hoe₁, disjoint_comm]
  let g := ![p₁', p₂', (q₂ - p₁')]
  have hg : evalOne (g 1) = 0 := by
    refine evalOne_stronglyHomogeneous_decomposition g ?_ ?_ hf hp₁ hIp₁ 0 ?_ hp₁z 1 (by simp)
    · rw [Fin.sum_univ_three]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, g, hs₂]
      ring
    · intro i j
      fin_cases i
      · fin_cases j
        · simp
        · simpa [g]
        · simpa [g]
      · fin_cases j
        · simp [g]
        · simp [g]
        · simpa [g]
      · grind
    · intro i
      fin_cases i
      · simp
      · simpa [g]
      · simpa [g]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, g] at hg
  exact he₂ hp₂z hg

end CommRing

section Finite

variable [Finite α]

lemma symmSet_finite_of_finite (f : MvPolynomial α R) : (symmSet {f}).Finite := by
  simp only [symmSet, Set.image_singleton, Set.iUnion_singleton_eq_range]
  exact Set.finite_range _

lemma mgs_le_factorial_of_isPSI (h : IsPrincipalSymmetric I) :
    minGenSize I ≤ (Nat.card α).factorial := by
  classical
  obtain ⟨f, h⟩ := h
  by_cases hf0 : f = 0
  · simp_all
  have := (symmSet_finite_of_finite f).fintype
  have hc : (symmSet {f}).toFinset.card ≤ (Nat.card α).factorial := by
    rw [← Nat.card_perm, ← Nat.card_eq_card_toFinset]
    refine Nat.card_le_card_of_injective (fun ⟨g, hg⟩ ↦
      Classical.choose (mem_symmSet_singleton.mp hg)) ?_
    intro ⟨g, hg⟩ ⟨g', hg'⟩
    simp only [Subtype.mk.injEq]
    intro h
    rw [← Classical.choose_spec (mem_symmSet_singleton.mp hg),
      ← Classical.choose_spec (mem_symmSet_singleton.mp hg'), h]
  refine le_trans ?_ hc
  refine Nat.sInf_le ?_
  simp only [Set.mem_image, Set.mem_setOf_eq]
  use (symmSet {f}).toFinset
  constructor
  · constructor
    · simp [zero_notMem_symmSet_of_ne_zero hf0]
    · simp [h]
  · rfl


lemma mgs_le_finrank_orderTypeComponent_sub_one {R : Type*} [Field R]
    {p : MvPolynomial α R} {a : Multiset ℕ}
    (hp : p.IsStronglyHomogeneous a) (hp0 : p ≠ 0) (hp1 : evalOne p = 0) :
    minGenSize (symmSpan {p}) ≤ Module.finrank R (orderTypeComponent α R a) - 1 := by
  rw [← homogSubI_orderTypeComponent a, ← mgs_eq_finrank (isSingleDegGen_orderTypeComponent a)]
  refine Nat.le_sub_one_of_lt ?_
  refine mgs_lt_mgs ?_ ?_ ?_ ?_
  · exact isSingleDegGen_symmSpan (isHomogeneous_of_isStronglyHomogeneous a hp)
  · exact isSingleDegGen_orderTypeComponent a
  · exact minDeg_stronglyHomogeneous_symmSpan hp hp0
  · exact symmSpan_lt_span_orderTypeComponent hp hp0 hp1

end Finite
