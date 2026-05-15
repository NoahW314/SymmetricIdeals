/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Upstream

variable {α R : Type*} [CommSemiring R]

open MvPolynomial Equiv

namespace Rename

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable
instance SymmetricAction : MulSemiringAction (Perm α) (MvPolynomial α R) where
  smul σ p := rename σ p
  one_smul := rename_id_apply
  mul_smul := by simp [HSMul.hSMul]
  smul_zero σ := by simp [HSMul.hSMul]
  smul_add σ p q := by simp [HSMul.hSMul]
  smul_one σ := by simp [HSMul.hSMul]
  smul_mul σ p q := by simp [HSMul.hSMul]

lemma symmAct_def (σ : Perm α) (p : MvPolynomial α R) : σ • p = rename σ p := by rfl

lemma perm_isHomogeneous (σ : Perm α) {p : MvPolynomial α R} {n : ℕ} (h : p.IsHomogeneous n) :
    (σ • p).IsHomogeneous n := by
  rw [symmAct_def]
  exact IsHomogeneous.rename_isHomogeneous h

@[simp]
lemma symmAct_homogeneousComponent {σ : Perm α} {p : MvPolynomial α R} {n : ℕ} :
    σ • (homogeneousComponent n p) = homogeneousComponent n (σ • p) := by
  rw [symmAct_def, symmAct_def]
  exact rename_homogeneousComponent σ.injective

@[simp]
lemma perm_monomial {σ : Equiv.Perm α} {d : α →₀ ℕ} {c : R} :
    σ • (monomial d c) = monomial (Finsupp.mapDomain σ d) c := by
  simp [symmAct_def, rename_monomial]

lemma symm_totalDegree (p : MvPolynomial α R) (σ : Perm α) :
    p.totalDegree = (σ • p).totalDegree := by
  rw [symmAct_def, ← renameEquiv_apply, totalDegree_renameEquiv]

section IsSymmetric

noncomputable def IsSymmetric (S : Set (MvPolynomial α R)) :=
  ∀ σ : Perm α, ∀ f ∈ S, σ • f ∈ S

variable {S : Set (MvPolynomial α R)}

@[simp]
lemma perm_mem_of_mem {p : MvPolynomial α R} {σ : Perm α}
    (hS : IsSymmetric S) (h : p ∈ S) : σ • p ∈ S := by
  exact hS σ p h

lemma mem_iff_perm_mem_of_isSymmetric {p : MvPolynomial α R} {σ : Perm α} (h : IsSymmetric S) :
    p ∈ S ↔ σ • p ∈ S := by
  constructor
  · exact perm_mem_of_mem h
  · intro h'
    apply perm_mem_of_mem (σ := σ⁻¹) h at h'
    simpa using h'

lemma isSymmetric_iff_rename_map_eq : IsSymmetric S ↔ ∀ σ : Perm α, (rename σ) '' S = S := by
  constructor
  · intro h σ
    ext f
    rw [Set.mem_image]
    constructor
    · intro ⟨g, hi, hg⟩
      rw [← hg]
      exact h σ g hi
    · intro hi
      use σ⁻¹ • f
      constructor
      · exact h σ⁻¹ f hi
      simp [symmAct_def]
  · intro h σ f hi
    rw [← h σ]
    use f
    simp [hi, symmAct_def]

@[simp]
lemma rename_isSymmetric {σ : Perm α} (h : IsSymmetric S) :
    (rename σ) '' S = S := isSymmetric_iff_rename_map_eq.mp h σ


/-- the symmetric closure of S -/
def symmSet (S : Set (MvPolynomial α R)) : Set (MvPolynomial α R) := ⋃ σ : Perm α, ((σ • ·) '' S)

lemma mem_symmSet {f : MvPolynomial α R} :
    f ∈ symmSet S ↔ ∃ σ : Perm α, ∃ g ∈ S, σ • g = f := by
  simp [symmSet]

@[simp]
lemma self_le_symmSet : S ≤ symmSet S := by
  intro x hx
  simp only [symmSet, Set.mem_iUnion, Set.mem_image]
  use 1, x, hx
  simp

@[simp]
lemma isSymmetric_symmSet : IsSymmetric (symmSet S) := by
  intro σ f
  simp only [mem_symmSet, forall_exists_index, and_imp]
  intro τ g hg hf
  subst hf
  use σ * τ, g, hg
  rw [mul_smul]

lemma isSymmetric_iff_symmSet_eq : IsSymmetric S ↔ symmSet S = S := by
  constructor
  · intro h
    refine le_antisymm ?_ self_le_symmSet
    intro f
    simp only [mem_symmSet, forall_exists_index, and_imp]
    intro σ g hg hf
    subst hf
    exact h σ g hg
  · intro h
    exact h ▸ isSymmetric_symmSet

lemma symmSet_mono : Monotone (symmSet (α := α) (R := R)) := by
  intro S T h
  refine Set.iUnion_mono ?_
  simp [Set.image_mono h]

lemma symmSet_symmSet : symmSet (symmSet S) = symmSet S := by
  rw [← isSymmetric_iff_symmSet_eq]
  exact isSymmetric_symmSet

lemma symmSet_le_iff {T : Set (MvPolynomial α R)} (h : IsSymmetric T) :
    symmSet S ≤ T ↔ S ≤ T := by
  constructor
  · exact le_trans self_le_symmSet
  · rw [isSymmetric_iff_symmSet_eq] at h
    nth_rw 2 [← h]
    intro h'
    exact symmSet_mono h'


@[simp]
lemma symmSet_zero : symmSet {(0 : MvPolynomial α R)} = {0} := by simp [symmSet]

@[simp]
lemma symmSet_one : symmSet {(1 : MvPolynomial α R)} = {1} := by simp [symmSet]

noncomputable
abbrev symmSpan (S : Set (MvPolynomial α R)) : Ideal (MvPolynomial α R) := Ideal.span (symmSet S)

@[simp]
lemma symmSpan_zero : symmSpan {(0 : MvPolynomial α R)} = ⊥ := by simp

@[simp]
lemma symmSpan_one : symmSpan {(1 : MvPolynomial α R)} = ⊤ := by simp [symmSpan]

lemma subset_symmSpan : S ⊆ symmSpan S :=
  le_trans Ideal.subset_span <| Ideal.span_mono self_le_symmSet

lemma span_isSymmetric {S : Set (MvPolynomial α R)} (h : IsSymmetric S) :
    IsSymmetric (SetLike.coe (Ideal.span S)) := by
  rw [isSymmetric_iff_rename_map_eq]
  intro σ
  conv => rhs; rw [← rename_isSymmetric h (σ := σ), ← Ideal.map_span]
  exact (Ideal.map_eq_image_of_surjective _ <| rename_surjective _ σ.surjective).symm

@[simp]
lemma isSymmetric_symmSpan : IsSymmetric (SetLike.coe (symmSpan S)) :=
  span_isSymmetric isSymmetric_symmSet

lemma isSymmetric_iff_eq_symmSpan {I : Ideal (MvPolynomial α R)} :
    IsSymmetric (SetLike.coe I) ↔ symmSpan I = I := by
  constructor
  · intro h
    rw [symmSpan, isSymmetric_iff_symmSet_eq.mp h, Ideal.span_eq]
  · intro h
    exact h ▸ isSymmetric_symmSpan

lemma symmSpan_le_iff_le {I : Ideal (MvPolynomial α R)}
    (h : IsSymmetric (SetLike.coe I)) : symmSpan S ≤ I ↔ S ≤ I := by
  rw [← symmSet_le_iff h, Ideal.span_le, Set.le_iff_subset]

end IsSymmetric

section IsPrincipalSymmetric

lemma mem_symmSet_singleton {p q : MvPolynomial α R} :
    q ∈ symmSet {p} ↔ ∃ σ : Perm α, σ • p = q := by
  simp [symmSet]

lemma mem_symmSet_singleton_of_perm {p : MvPolynomial α R} {σ : Perm α} : σ • p ∈ symmSet {p} := by
  simp [mem_symmSet_singleton]

@[simp]
lemma self_mem_symmSet {p : MvPolynomial α R} : p ∈ symmSet {p} := by
  simp only [mem_symmSet, Set.mem_singleton_iff, exists_eq_left]
  use 1
  simp

@[simp]
lemma mem_symmSet_singleton_self {p : MvPolynomial α R} : p ∈ symmSet {p} := by
  rw [mem_symmSet_singleton]
  use 1; apply one_smul

lemma zero_notMem_symmSet_of_ne_zero {f : MvPolynomial α R} (h : f ≠ 0) : 0 ∉ symmSet {f} := by
  simpa [smul_eq_zero_iff_eq, mem_symmSet_singleton]

lemma symmSet_subset_homogSub_of_isHomogeneous {n : ℕ} {p : MvPolynomial α R}
    (h : p.IsHomogeneous n) : symmSet {p} ⊆ (homogeneousSubmodule α R n) := by
  intro q hq
  rw [mem_symmSet_singleton] at hq
  obtain ⟨σ, hq⟩ := hq
  rw [← hq]
  simp only [SetLike.mem_coe, mem_homogeneousSubmodule]
  exact perm_isHomogeneous σ h

lemma symmSet_singleton_eq_range {p : MvPolynomial α R} :
    symmSet {p} = Set.range (fun σ : Equiv.Perm α => σ • p) := by
  simp [symmSet]

@[simp]
lemma mem_symmSpan_self {p : MvPolynomial α R} : p ∈ symmSpan {p} :=
  Submodule.mem_span_of_mem mem_symmSet_singleton_self

lemma symmSpan_eq_bot_iff {p : MvPolynomial α R} : symmSpan {p} = ⊥ ↔ p = 0 := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff] at h
    exact h p mem_symmSpan_self
  · intro h
    simp [h]

lemma mem_symmSpan_monomial {d : α →₀ ℕ} (σ : Perm α) :
    monomial (Finsupp.mapDomain σ d) (1 : R) ∈ symmSpan {(monomial d (1 : R))} := by
  refine Submodule.mem_span_of_mem ?_
  simp [perm_monomial, mem_symmSet_singleton]

lemma symmSpan_sum_le_sup_symmSpan {X : Type*} {S : Finset X} {g : S → MvPolynomial α R} :
    symmSpan {∑ a, g a} ≤ ⨆ a, symmSpan {g a} := by
  rw [← Submodule.span_iUnion, Submodule.span_le]
  intro p hp
  rw [mem_symmSet_singleton] at hp
  obtain ⟨σ, hp⟩ := hp
  rw [← hp, Finset.smul_sum]
  refine Submodule.sum_mem _ ?_
  intro a ha
  refine Submodule.subset_span ?_
  simp [mem_symmSet_singleton]

lemma symmSpan_singleton_le_iff_mem {p : MvPolynomial α R} {I : Ideal (MvPolynomial α R)}
    (h : IsSymmetric (SetLike.coe I)) : symmSpan {p} ≤ I ↔ p ∈ I := by
  simp [symmSpan_le_iff_le h]

lemma symmSpan_singleton_le_of_mem {p q : MvPolynomial α R} (h : q ∈ symmSpan {p}) :
    symmSpan {q} ≤ symmSpan {p} := by
  rwa [symmSpan_singleton_le_iff_mem isSymmetric_symmSpan]

noncomputable def IsPrincipalSymmetric (I : Ideal (MvPolynomial α R)) := ∃ f : MvPolynomial α R,
  I = symmSpan {f}

lemma isSymmetric_of_isPSI {I : Ideal (MvPolynomial α R)} (h : IsPrincipalSymmetric I) :
    IsSymmetric (SetLike.coe I) := by
  obtain ⟨f, h⟩ := h
  rw [h]
  exact isSymmetric_symmSpan

@[simp]
lemma isPSI_top : IsPrincipalSymmetric (⊤ : Ideal (MvPolynomial α R)) := by
  use 1; exact symmSpan_one.symm

@[simp]
lemma isPSI_bot : IsPrincipalSymmetric (⊥ : Ideal (MvPolynomial α R)) := by
  use 0; exact symmSpan_zero.symm

end IsPrincipalSymmetric

end Rename
