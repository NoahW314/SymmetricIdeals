/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Symmetry.Basic

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

open MvPolynomial Rename Equiv
open scoped Pointwise

def kSymmetric (p : MvPolynomial α R) := ∀ σ : Equiv.Perm α, ∃ c : R, σ • p = c • p

@[simp]
lemma kSymmetric_zero : kSymmetric (0 : MvPolynomial α R) := by
  intro σ
  use 1
  simp only [smul_zero]

@[simp]
lemma kSymmetric_one : kSymmetric (1 : MvPolynomial α R) := by
  intro σ
  use 1
  simp

lemma kSymmetric_C_mul {p : MvPolynomial α R} (c : R) (h : kSymmetric p) :
    kSymmetric (C c * p) := by
  intro σ
  obtain ⟨d, h⟩ := h σ
  use d
  simp [symmAct_def, h]

lemma kSymmetric_C_mul' {p : MvPolynomial α R} (c : R) (h : kSymmetric p) :
    kSymmetric (p * C c) := by
  rw [mul_comm]
  exact kSymmetric_C_mul c h

lemma perm_kSymmetric {p : MvPolynomial α R} (σ : Perm α) (h : kSymmetric p) :
    kSymmetric (σ • p) := by
  obtain ⟨c, h'⟩ := h σ
  rw [h', smul_eq_C_mul]
  exact kSymmetric_C_mul c h

lemma perm_eq_c_perm_of_kSymmetric {p : MvPolynomial α R} (h : kSymmetric p) :
    ∀ σ τ : Equiv.Perm α, ∃ c : R, σ • p = c • (τ • p) := by
  intro σ τ
  obtain ⟨c, h⟩ := (perm_kSymmetric τ h) (σ * τ⁻¹)
  simp [← mul_smul] at h
  use c

lemma symmSpan_ne_bot_of_not_kSymmetric {p : MvPolynomial α R} (h : ¬kSymmetric p) :
    symmSpan {p} ≠ ⊥ := by
  contrapose! h
  rw [symmSpan_eq_bot_iff] at h
  simp [h]

lemma kSymmetric_monomial_iff [Nontrivial R] {d : α →₀ ℕ} :
    kSymmetric (monomial d (1 : R)) ↔ ∃ n, ∀ x : α, d x = n := by
  classical
  constructor
  · intro h
    by_cases! hα : Nonempty α
    · obtain ⟨y⟩ := hα
      use d y
      intro x
      specialize h (swap x y)
      obtain ⟨c, h⟩ := h
      simp only [perm_monomial, smul_eq_C_mul, C_mul_monomial, mul_one, monomial_eq_monomial_iff,
        one_ne_zero, false_and, or_false] at h
      apply And.left at h
      have h : (Finsupp.mapDomain (swap x y) d) x = d x := congrFun (congrArg DFunLike.coe h) x
      simp only [Finsupp.mapDomain_equiv_apply, symm_swap, swap_apply_left] at h
      exact h.symm
    · use 0
      simp only [IsEmpty.forall_iff]
  · intro ⟨n, h⟩ σ
    use 1
    simp only [perm_monomial, one_smul, ne_eq, one_ne_zero, not_false_eq_true,
      monomial_left_inj]
    ext x
    rw [h x, Finsupp.mapDomain_equiv_apply, h (Equiv.symm σ x)]

lemma symmSpan_eq_span_of_kSymmetric {p : MvPolynomial α R} (h : kSymmetric p) :
    symmSpan {p} = Ideal.span {p} := by
  refine Submodule.span_eq_span ?_ ?_
  · intro x
    simp only [mem_symmSet_singleton, SetLike.mem_coe, Ideal.mem_span_singleton,
      forall_exists_index]
    intro σ hσ
    obtain ⟨c, h⟩ := h σ
    simp [← hσ, h, smul_eq_C_mul]
  · simp

theorem mul_symmSpan_of_kSymmetric {p q : MvPolynomial α R} (h : kSymmetric p) :
    symmSpan {p} * symmSpan {q} = symmSpan {p * q} := by
  rw [Ideal.span_mul_span]
  refine Submodule.span_eq_span ?_ ?_
  · intro f hf
    simp only [Set.mem_mul, mem_symmSet_singleton, exists_exists_eq_and] at hf
    obtain ⟨σ, τ, hf⟩ := hf
    obtain ⟨c, hc⟩ := perm_eq_c_perm_of_kSymmetric h σ τ
    rw [← hf, hc]
    simp only [smul_eq_C_mul, mul_assoc, SetLike.mem_coe]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.mem_span_of_mem ?_
    simp [mem_symmSet_singleton]
  · intro f hf
    rw [mem_symmSet_singleton] at hf
    obtain ⟨σ, hf⟩ := hf
    refine Submodule.mem_span_of_mem ?_
    simp [← hf, Set.mem_mul, mem_symmSet_singleton]

lemma symmSpan_pow_of_kSymmetric {p : MvPolynomial α R} (h : kSymmetric p) (n : ℕ) :
    symmSpan {p} ^ n = symmSpan {p ^ n} := by
  induction n
  · simp
  · rename_i n ih
    simp [pow_succ, ih, mul_comm, mul_symmSpan_of_kSymmetric h]
