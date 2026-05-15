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

theorem span_union_homogeneousComponent_image {S : Set (MvPolynomial α R)} (h : I = Ideal.span S)
    (hI : I.IsHomogeneous (homogeneousSubmodule α R)) :
    I = Ideal.span (⋃ n, homogeneousComponent n '' S) := by
  subst h
  refine Submodule.span_eq_span ?_ ?_
  · intro f hf
    rw [← sum_homogeneousComponent f]
    refine Submodule.sum_mem _ ?_
    intro n _
    refine Submodule.mem_span_of_mem ?_
    rw [Set.mem_iUnion]
    use n, f
  · intro f
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp]
    intro n g hg hf
    subst hf
    exact homogeneousComponent_mem_of_mem hI (Submodule.mem_span_of_mem hg) n


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

lemma homogeneousComponent_mul {α R : Type*} [CommSemiring R] {f g : MvPolynomial α R} {n : ℕ} :
    homogeneousComponent n (f * g) = ∑ d ∈ Finset.antidiagonal n,
    homogeneousComponent d.1 f * homogeneousComponent d.2 g := by
  ext c
  classical simp only [coeff_homogeneousComponent, coeff_mul, coeff_sum, mul_ite, ite_mul, zero_mul,
    mul_zero]
  split_ifs with h
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.sum_eq_single_of_mem (x.1.degree, x.2.degree)]
    · simp
    · simp at hx
      simp [← h, ← map_add, hx]
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

lemma mem_span_homogeneousSubmodule {n m : ℕ} {f : MvPolynomial α R} (h : f.IsHomogeneous n)
    (hnm : n ≥ m) : f ∈ Ideal.span (homogeneousSubmodule α R m) := by
  rw [as_sum f]
  refine Ideal.sum_mem _ ?_
  intro c hc
  apply IsHomogeneous.degree_eq_sum_deg_support h at hc
  rw [hc] at hnm
  obtain ⟨d, hdc, hdm⟩ := Finsupp.exists_le_degree_eq _ _ hnm
  obtain ⟨e, he⟩ := exists_add_of_le hdc
  rw [← one_mul (coeff c f), he, ← monomial_mul]
  refine Ideal.mul_mem_right _ _ ?_
  refine Submodule.mem_span_of_mem ?_
  simp [isHomogeneous_monomial _ hdm]

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
  · simp [le_inf_iff, Submodule.span_le, h]

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
