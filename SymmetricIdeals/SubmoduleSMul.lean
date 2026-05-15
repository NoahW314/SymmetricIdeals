/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Symmetry.Basic
import SymmetricIdeals.Symmetry.kSymmetric
import SymmetricIdeals.Upstream

variable {R S : Type*} [Semiring R] [Semiring S] [Module R S] [SMulCommClass R S S]

abbrev pmul (p : S) (M : Submodule R S) := Submodule.map (LinearMap.mulLeft R p) M

variable {p q : S} {M : Submodule R S}

lemma mem_pmul_of_mul_mem (p q) (hq : q ∈ M) : p * q ∈ pmul p M := by
  rw [Submodule.mem_map]
  use q
  simp [hq]


lemma pmul_bij [IsDomain S] (p) (hp : p ≠ 0) : Function.Bijective
    (fun q ↦ ⟨LinearMap.mulLeft R p q, Submodule.apply_coe_mem_map _ q⟩ : M → pmul p M) := by
  constructor
  · intro x y hxy
    simpa [hp] using hxy
  · intro ⟨q, hq⟩
    simpa using hq

lemma pmul_restrict_bij [IsDomain S] (p : S) (hp : p ≠ 0) : Function.Bijective
    ((LinearMap.mulLeft R p).restrict (fun _ ↦ Submodule.mem_map_of_mem (p := M))) := by
  convert (pmul_bij p hp)

noncomputable
def pmulEquiv [IsDomain S] (p : S) (M : Submodule R S) (hp : p ≠ 0) :
    M ≃ₗ[R] (pmul p M) := LinearEquiv.ofBijective _ (pmul_restrict_bij p hp)

lemma rank_eq_pmul_rank [IsDomain S] (p) (hp : p ≠ 0) :
  Module.finrank R M = Module.finrank R (pmul p M) := LinearEquiv.finrank_eq (pmulEquiv p M hp)


lemma dvd_of_mem_pmul (h : q ∈ pmul p M) : p ∣ q := by
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply] at h
  obtain ⟨r, hr, h⟩ := h
  use r
  exact h.symm

lemma pmul_inf [IsDomain S] {N : Submodule R S} :
    pmul p (M ⊓ N) = (pmul p M) ⊓ (pmul p N) := by
  by_cases hp0 : p = 0
  · simp [pmul, hp0]
  rw [pmul, Submodule.map_inf]
  intro x y
  simp [hp0]

variable {S : Type*} [CommSemiring S] {I J : Ideal S} {p : S}

lemma pmul_eq_span_mul : pmul p I = Ideal.span {p} * I := by
  rw [pmul, ← Submodule.top_smul I, smul_eq_mul, mul_comm ⊤, ← smul_eq_mul,
    Submodule.map_smul'' I ⊤ _]
  simp [LinearMap.mulLeft_range, mul_comm]

lemma pmul_mul : pmul p (I * J) = (pmul p I) * J := by
  rw [pmul_eq_span_mul, pmul_eq_span_mul, mul_assoc]

lemma pmul_mul' : pmul p (I * J) = I * (pmul p J) := by
  rw [mul_comm, pmul_mul, mul_comm]


section MvPolynomial

open MvPolynomial Rename

variable {α R : Type*} [CommSemiring R]

lemma symmSpan_eq_pmul_symmSpan {p q r : MvPolynomial α R} (h : p = q * r) (hq : kSymmetric q) :
    symmSpan {p} = pmul q (symmSpan {r}) := by
  rw [pmul_eq_span_mul, ← symmSpan_eq_span_of_kSymmetric hq, mul_symmSpan_of_kSymmetric hq, h]

lemma pmul_restrictScalars {p : MvPolynomial α R} {I : Ideal (MvPolynomial α R)} :
    pmul p (Submodule.restrictScalars R I) = Submodule.restrictScalars R (pmul p I) := by
  simp [pmul, Submodule.restrictScalars_map, LinearMap.restrictScalars_mulLeft]

lemma pmul_perm_le_symmSpan_mul {p : MvPolynomial α R} {σ : Equiv.Perm α}
    {J : Ideal (MvPolynomial α R)} : pmul (σ • p) J ≤ symmSpan {p} * J := by
  rw [pmul_eq_span_mul]
  exact Ideal.mul_mono_left <| Ideal.span_mono (by simp)

lemma pmul_le_symmSpan_mul {p : MvPolynomial α R} {J : Ideal (MvPolynomial α R)} :
    pmul p J ≤ symmSpan {p} * J := by
  nth_rw 1 [← one_smul (Equiv.Perm α) p]
  exact pmul_perm_le_symmSpan_mul

end MvPolynomial
