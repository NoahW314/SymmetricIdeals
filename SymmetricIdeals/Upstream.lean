/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib


open MvPolynomial

-- simp only [Finset.mem_filter, mem_support_iff, ne_eq, and_imp]
-- intro c _ _ d _ _ hcd
-- exact Finsupp.mapDomain_injective h hcd

lemma rename_homogeneousComponent {α R ι : Type*} [CommSemiring R] {φ : α → ι}
    {p : MvPolynomial α R} {n : ℕ} (h : Function.Injective φ) :
    rename φ (homogeneousComponent n p) = homogeneousComponent n (rename φ p) := by
  simp only [homogeneousComponent_apply n p, map_sum, rename_monomial, homogeneousComponent_apply]
  refine Finset.sum_bij (fun d _ ↦ Finsupp.mapDomain φ d) ?_ ?_ ?_ ?_
  · simp [coeff_rename_mapDomain _ h]
  · grind [Finsupp.mapDomain_injective]
  · classical simp only [Finset.mem_filter, support_rename_of_injective h, exists_prop, and_imp,
      Finset.mem_image]
    grind [Finsupp.degree_mapDomain]
  · simp [coeff_rename_mapDomain _ h]

lemma Ideal.map_eq_image_of_surjective {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    (f : F) [RingHomClass F R S] (hf : Function.Surjective ⇑f) {I : Ideal R} :
    Ideal.map f I = ⇑f '' ↑I := by
  ext y
  simp [Ideal.mem_map_iff_of_surjective f hf]

lemma homogeneousSubmodule_fg {α R : Type*} [Finite α] [CommSemiring R] (n : ℕ) :
    (homogeneousSubmodule α R n).FG := by
  rw [homogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
  suffices Finite {d : α →₀ ℕ | d.degree = n} by
    exact Module.Finite.of_basis (basisRestrictSupport R {d | d.degree = n})
  have : Finite {d : α →₀ ℕ | ∀ a, d a ≤ n} :=
    ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype
  apply Finite.Set.subset {d : α →₀ ℕ | ∀ a, d a ≤ n}
  rw [Set.setOf_subset_setOf]
  intro d hd a
  rw [← hd]
  exact Finsupp.le_degree a d

attribute [local instance] MvPolynomial.gradedAlgebra

lemma mem_iff_homogeneousComponent_mem {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}
    (h : I.IsHomogeneous (homogeneousSubmodule α R)) {f : MvPolynomial α R} :
    f ∈ I ↔ ∀ n, (homogeneousComponent n f) ∈ I := by
  simp_rw [← decomposition.decompose'_apply]
  exact h.mem_iff

lemma homogeneousComponent_mem_of_mem {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}
    {f : MvPolynomial α R} (h : I.IsHomogeneous (homogeneousSubmodule α R)) (hf : f ∈ I) (n : ℕ) :
    (homogeneousComponent n f) ∈ I :=
  (mem_iff_homogeneousComponent_mem h).mp hf n

attribute [local instance] MvPolynomial.weightedGradedAlgebra

lemma mem_iff_weightedHomogeneousComponent_mem {α R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [DecidableEq M] {I : Ideal (MvPolynomial α R)} (w : α → M)
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {f : MvPolynomial α R} :
    f ∈ I ↔ ∀ m : M, (weightedHomogeneousComponent w m f) ∈ I := by
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact h.mem_iff

lemma weightedHomogeneousComponent_mem_of_mem {α R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [DecidableEq M] {I : Ideal (MvPolynomial α R)} {f : MvPolynomial α R}
    (w : α → M) (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (hf : f ∈ I) (m : M) :
    (weightedHomogeneousComponent w m f) ∈ I :=
  (mem_iff_weightedHomogeneousComponent_mem w h).mp hf m



lemma isHomogeneous_zero_of_isEmpty {α R : Type*} [CommSemiring R] [IsEmpty α]
    (f : MvPolynomial α R) : f.IsHomogeneous 0 := by
  rw [eq_C_of_isEmpty f]
  exact isHomogeneous_C α (coeff 0 f)



lemma LinearMap.mulLeft_range {S : Type*} [CommSemiring S] {p : S} :
    (LinearMap.mulLeft S p).range = Ideal.span {p} := by
  ext x
  simp [Ideal.mem_span_singleton', mul_comm]

lemma LinearMap.mulRight_range {S : Type*} [Semiring S] {p : S} :
    (LinearMap.mulRight S p).range = Ideal.span {p} := by
  ext x
  simp [Ideal.mem_span_singleton']

lemma LinearMap.restrictScalars_mulLeft (R : Type*) {S : Type*} [Semiring R] [CommSemiring S]
    [Module R S] [LinearMap.CompatibleSMul S S R S] [SMulCommClass R S S] (p : S) :
    LinearMap.restrictScalars R (LinearMap.mulLeft S p) = LinearMap.mulLeft R p := by
  ext x
  simp

lemma LinearMap.restrictScalars_mulRight (R : Type*) {S : Type*} [Semiring R] [CommSemiring S]
    [Module R S] [LinearMap.CompatibleSMul S S R S] [IsScalarTower R S S] (p : S) :
    LinearMap.restrictScalars R (LinearMap.mulRight S p) = LinearMap.mulRight R p := by
  ext x
  simp



lemma csSup_eq_bot_iff {X : Type*} [ConditionallyCompleteLinearOrderBot X] {s : Set X}
    (h : BddAbove s) : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  constructor
  · contrapose!
    intro ⟨hne, hs⟩
    simp_rw [← bot_lt_iff_ne_bot, lt_csSup_iff h hne, bot_lt_iff_ne_bot]
    contrapose! hs
    exact hne.subset_singleton_iff.mp hs
  · intro hs
    rcases hs with hs | hs <;> simp [hs]

lemma range_subset_range_mapDomain {α β M : Type*} [AddCommMonoid M] {f : α → β} (v : α →₀ M)
    (h : Function.Injective f) : Set.range v ⊆ Set.range (Finsupp.mapDomain f v) := by
  intro y
  simp only [Set.mem_range, forall_exists_index]
  intro x hx
  use f x
  rw [Finsupp.mapDomain_apply h, hx]

lemma range_mapDomain_of_equiv {α β M : Type*} [AddCommMonoid M] (f : α ≃ β) (v : α →₀ M) :
    Set.range (Finsupp.mapDomain f v) = Set.range v := by
  refine le_antisymm ?_ (range_subset_range_mapDomain v f.injective)
  intro y
  simp only [Set.mem_range, forall_exists_index]
  intro x hx
  use f.symm x
  simp [← hx]


lemma mul_dvd_left_iff_isUnit {α : Type*} [Zero α] [CommMonoid α] [IsLeftCancelMulZero α]
    {f g : α} (hf0 : f ≠ 0) : f * g ∣ f ↔ IsUnit g := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    nth_rw 1 [← mul_one f] at hu
    rw [mul_assoc, mul_right_inj' hf0] at hu
    exact IsUnit.of_mul_eq_one u hu.symm
  · intro h
    rw [h.mul_right_dvd]

lemma mul_dvd_right_iff_isUnit {α : Type*} [Zero α] [CommMonoid α] [IsLeftCancelMulZero α]
    {f g : α} (hf0 : f ≠ 0) : g * f ∣ f ↔ IsUnit g := by
  rw [mul_comm]
  exact mul_dvd_left_iff_isUnit hf0

lemma dvd_of_mem_span {α : Type*} [CommSemiring α] {x y : α} {s : Set α} (h : ∀ z ∈ s, x ∣ z)
    (hy : y ∈ Ideal.span s) : x ∣ y := by
  obtain ⟨f, t, hr, hft, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hy
  refine Finset.dvd_sum ?_
  intro i hi
  rw [smul_eq_mul]
  exact Dvd.dvd.mul_left (h i (hr hi)) (f i)

lemma Ideal.span_sdiff_singleton_zero' {α : Type*} [DecidableEq α] [Semiring α] {s : Finset α} :
    Ideal.span (s \ {0} : Finset α) = Ideal.span (SetLike.coe s) := by simp
