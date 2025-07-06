import Mathlib
import SymmetricIdeals.Basic

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

open MvPolynomial

def kSymmetric (p : MvPolynomial α F) := ∀ σ : Equiv.Perm α, ∃ c : F, σ • p = c • p

lemma kSymmetric_zero : kSymmetric (0 : MvPolynomial α F) := by
  intro σ; use 1; simp only [smul_zero]

lemma kSymmetric_iff_nonzero_c {p : MvPolynomial α F} : kSymmetric p ↔
  ∀ σ : Equiv.Perm α, ∃ c : F, c ≠ 0 ∧ σ • p = c • p := by
    constructor
    intro h σ
    by_cases hpz : p = 0
    use 1; constructor; exact one_ne_zero
    rw [hpz, smul_zero, smul_zero]

    obtain ⟨c, h⟩ := h σ
    use c; constructor; swap; exact h
    contrapose! hpz
    rw [hpz, zero_smul] at h
    apply_fun (σ⁻¹ • .) at h
    rw [inv_smul_smul, smul_zero] at h
    exact h

    intro h σ
    specialize h σ
    obtain ⟨c, h⟩ := h
    use c; exact h.2

lemma perm_eq_c_perm_of_kSymm {p : MvPolynomial α F} (h : kSymmetric p) : ∀ σ τ : Equiv.Perm α,
  ∃ c : F, σ • p = c • (τ • p) := by
    intro σ τ
    obtain ⟨c₁, hc₁⟩ := h σ
    obtain ⟨c₂, hc₂z, hc₂⟩ := (kSymmetric_iff_nonzero_c.mp h) τ
    use c₁ * c₂⁻¹
    rw [hc₂, hc₁, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    rw [← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ hc₂z, mul_one]

lemma symmSpan_not_bot_of_not_kSymmetric {p : MvPolynomial α F} (h : ¬ kSymmetric p) :
  symmSpan {p} ≠ ⊥ := by
    contrapose! h
    rw [symmSpan_bot_iff] at h
    rw [h]; exact kSymmetric_zero

theorem productPsi_of_kSymmetric {p q : MvPolynomial α F} (h : kSymmetric p) :
  (symmSpan {p})*(symmSpan {q}) = symmSpan {p*q} := by
    unfold symmSpan
    rw [Ideal.span_mul_span]
    apply Submodule.span_eq_span

    intro f hf
    simp only [mem_symmSet_singleton, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range] at hf
    obtain ⟨σ, τ, hf⟩ := hf
    obtain ⟨c, hc⟩ := perm_eq_c_perm_of_kSymm h σ τ
    rw [← hf, hc]
    simp only [Ideal.submodule_span_eq, Algebra.smul_mul_assoc, SetLike.mem_coe]
    rw [← smul_mul', smul_eq_C_mul]
    apply Ideal.mul_mem_left (Ideal.span (symmSet {p * q})) (C c)
    apply Submodule.subset_span
    exact mem_symmSet_singleton_of_perm


    intro f hf
    rw [mem_symmSet_singleton] at hf
    obtain ⟨σ, hf⟩ := hf
    rw [smul_mul'] at hf; rw [← hf]
    apply Submodule.subset_span
    simp only [mem_symmSet_singleton, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range, exists_apply_eq_apply2]

lemma powerPsi_of_kSymmetric {p : MvPolynomial α F} (h : kSymmetric p) (n : ℕ) :
  (symmSpan {p})^n = symmSpan {p^n} := by
    induction' n with n ih
    simp only [pow_zero, Ideal.one_eq_top, symmSpan_one]
    rw [pow_add, pow_one, pow_add, pow_one, ih, mul_comm, mul_comm (p^n)]
    exact productPsi_of_kSymmetric h
