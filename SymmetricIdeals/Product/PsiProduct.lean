/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Product.ProductMgs
import SymmetricIdeals.PrincipalSymmetric.PsiObstructions

/-!

-/

variable {α R : Type*} [CommSemiring R] [NoZeroDivisors R] {I : Ideal (MvPolynomial α R)}

open MvPolynomial Rename Equiv
attribute [local instance] MvPolynomial.gradedAlgebra

lemma exists_eq_smul_of_dvd (p : MvPolynomial α R) {σ : Perm α} (h : p ∣ σ • p) :
    ∃ c : R, σ • p = c • p := by
  by_cases! hp0 : p = 0
  · simp [hp0]
  obtain ⟨q, hq⟩ := h
  have hqd := hq
  apply_fun totalDegree at hqd
  rw [totalDegree_mul_of_isDomain hp0, symm_totalDegree p σ,
    Nat.left_eq_add, totalDegree_eq_zero_iff_eq_C] at hqd
  · use (coeff 0 q)
    rw [smul_eq_C_mul, ← hqd, mul_comm, hq]
  · contrapose! hp0
    rw [hp0, mul_zero] at hq
    exact (smul_eq_zero_iff_eq σ).mp hq

lemma mgs_eq_one_iff_kSymmetric (hI : IsSymmetric (SetLike.coe I))
    (hIB : I ≠ ⊥) : minGenSize I = 1 ↔ ∃ p, kSymmetric p ∧ I = symmSpan {p} := by
  constructor
  · intro h
    unfold minGenSize at h
    have hinf : (Finset.card '' {S | 0 ∉ S ∧ I = Ideal.span (SetLike.coe S)}).Nonempty := by
      contrapose! h
      simp [h]
    apply Nat.sInf_mem at hinf
    simp only [h, Set.mem_image, Set.mem_setOf_eq] at hinf
    obtain ⟨S, ⟨hS0, hSI⟩, hS1⟩ := hinf
    obtain ⟨p, hS1⟩ := Finset.card_eq_one.mp hS1
    use p
    rw [hS1, Finset.coe_singleton] at hSI
    suffices kSymmetric p by
      constructor
      · exact this
      · rw [hSI]
        exact (symmSpan_eq_span_of_kSymmetric this).symm
    intro σ
    refine exists_eq_smul_of_dvd p ?_
    rw [← Ideal.mem_span_singleton, ← hSI]
    refine hI σ _ ?_
    simp [hSI]
  · intro h
    obtain ⟨p, hp, hpI⟩ := h
    have hpS : 1 ∈ Finset.card '' {S | 0 ∉ S ∧ I = Ideal.span (SetLike.coe S)} := by
      simp only [Set.mem_image, Set.mem_setOf_eq]
      use {p}
      constructor
      constructor
      · simp only [Finset.mem_singleton, ne_eq]
        contrapose! hIB
        simp [hpI, ← hIB]
      · simp only [hpI, Finset.coe_singleton]
        exact symmSpan_eq_span_of_kSymmetric hp
      · simp
    refine le_antisymm (Nat.sInf_le hpS) <| le_csInf ?_ ?_
    · use 1
    intro n hn
    simp only [Set.mem_image, Set.mem_setOf_eq] at hn
    obtain ⟨S, ⟨hS0, hS⟩, hSn⟩ := hn
    contrapose! hIB
    simp at hIB
    simp [hIB] at hSn
    simp [hS, hSn]


lemma mgs_eq_one_iff_kSymmetric' {p : MvPolynomial α R} {n : ℕ} (hp : p.IsHomogeneous n)
    (hp0 : p ≠ 0) : minGenSize (symmSpan {p}) = 1 ↔ kSymmetric p := by
  have hps : IsPrincipalSymmetric (symmSpan {p}) := by use p
  rw [mgs_eq_one_iff_kSymmetric (isSymmetric_of_isPSI hps)]
  · constructor
    · intro ⟨q, hq, hpq⟩
      have hr : q ∣ p := by
        rw [← Ideal.mem_span_singleton, ← symmSpan_eq_span_of_kSymmetric hq, ← hpq]
        exact mem_symmSpan_self
      have hqp := hr
      obtain ⟨r, hr⟩ := hr
      have hpqr0 := hp0
      rw [hr, mul_ne_zero_iff] at hpqr0
      obtain ⟨hq0, hr0⟩ := hpqr0
      have hq2 := hq
      apply symmSpan_eq_pmul_symmSpan hr at hq
      rw [hpq] at hq
      apply_fun minDeg at hq
      have hqh : q.IsHomogeneous q.totalDegree := isHomogeneous_of_dvd_isHomogeneous hp hp0 hqp
      have hrh : r.IsHomogeneous r.totalDegree :=
        isHomogeneous_of_dvd_isHomogeneous hp hp0 <| Dvd.intro_left q hr.symm
      rw [minDeg_symmSpan hqh hq0, minDeg_pmul (isSingleDegGen_symmSpan hrh) hqh ?_ hq0,
        Nat.left_eq_add, minDeg_symmSpan hrh hr0, totalDegree_eq_zero_iff_eq_C] at hq
      · rw [hr, hq, mul_comm]
        exact kSymmetric_C_mul _ hq2
      · rwa [ne_eq, symmSpan_eq_bot_iff]
    · intro h
      use p
  · rwa [ne_eq, symmSpan_eq_bot_iff]

omit [NoZeroDivisors R] in
@[simp]
lemma pow_bot_isPSI (n : ℕ) : IsPrincipalSymmetric ((⊥ : Ideal (MvPolynomial α R)) ^ n) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [← Ideal.zero_eq_bot, zero_pow hn]
  simp

lemma pow_isPSI_of_mgs_one (hI : IsSymmetric (SetLike.coe I))
    (h : minGenSize I = 1) (n : ℕ) : IsPrincipalSymmetric (I ^ n) := by
  by_cases hIB : I = ⊥
  · rw [hIB]
    exact pow_bot_isPSI n
  · rw [mgs_eq_one_iff_kSymmetric hI hIB] at h
    obtain ⟨p, hp, hpI⟩ := h
    rw [hpI, symmSpan_pow_of_kSymmetric hp]
    use p ^ n

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {I : Ideal (MvPolynomial α R)}

theorem pow_monomial_isPSI_tfae (hI : IsSingleDegGen I)
    (hIm : ∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : R)) '' S))
    (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) :
    [∀ n : ℕ, IsPrincipalSymmetric (I ^ n), IsPrincipalSymmetric (I ^ 2),
    minGenSize I = 1].TFAE := by
  tfae_have 1 -> 2 := fun h ↦ h 2
  tfae_have 2 -> 3 := by
    by_cases! hR : Subsingleton R
    · simp [Subsingleton.allEq I ⊥] at hIB
    intro h
    simp only [pow_two, monomialProduct_Psi hIm hIm hIp hIp hI hI hIB hIB, or_self] at h
    obtain ⟨d, hk, hI⟩ := h
    simp [hI, mgs_eq_one_iff_kSymmetric' (isHomogeneous_monomial (1 : R) rfl), hk]
  tfae_have 3 -> 1 := pow_isPSI_of_mgs_one (isSymmetric_of_isPSI hIp)
  tfae_finish

theorem pow_monomial_isPSI_tfae' {d : α →₀ ℕ} :
    [∀ n, IsPrincipalSymmetric ((symmSpan {monomial d (1 : R)}) ^ n),
    IsPrincipalSymmetric ((symmSpan {monomial d (1 : R)}) ^ 2),
    kSymmetric (monomial d (1 : R))].TFAE := by
  by_cases! hd : monomial d (1 : R) = 0
  · simp [hd]
  rw [← mgs_eq_one_iff_kSymmetric' (isHomogeneous_monomial 1 rfl) hd]
  refine pow_monomial_isPSI_tfae ?_ ?_ ?_ ?_
  · exact isSingleDegGen_symmSpan (isHomogeneous_monomial 1 rfl)
  · use Set.range (fun σ : Equiv.Perm α => Finsupp.mapDomain σ d)
    unfold symmSpan; congr;
    ext e; simp only [mem_symmSet_singleton, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, symmAct_def, rename_monomial]
  · use (monomial d 1)
  · rwa [ne_eq, symmSpan_eq_bot_iff]

end CommRing

section Field

variable {α R : Type*} [Field R] [Finite α] {I : Ideal (MvPolynomial α R)}

theorem lt_mgs_pow {p : MvPolynomial α R} {m : ℕ} (n : ℕ)
    (hIB : I ≠ ⊥) (h : I = symmSpan {p}) (hp : p.IsHomogeneous m) (hpk : ¬kSymmetric p) :
    n < minGenSize (I ^ n) := by
  by_cases! hR : Subsingleton R
  · simp [Subsingleton.allEq I ⊥] at hIB
  induction n
  · simp only [pow_zero, Ideal.one_eq_top, mgs_top, zero_lt_one]
  · rename_i n ih
    rw [pow_succ]
    suffices minGenSize (I ^ n) + 1 ≤ minGenSize (I ^ n * I) by
      calc n + 1
        _ < minGenSize (I ^ n) + 1 := Nat.add_le_add_right ih 1
        _ ≤ minGenSize (I ^ n * I) := this
    nth_rw 3 [h]
    rw [mul_comm]
    have hI : IsSingleDegGen I := by
      rw [h]
      exact isSingleDegGen_symmSpan hp
    refine max_mgs_le_mgs_prod hp hpk (isSingleDegGen_pow hI n) ?_
    rw [← Ideal.zero_eq_bot] at hIB ⊢
    exact pow_ne_zero n hIB

theorem pow_isPSI_tfae {I : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I)
    (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) :
    [∀ n : ℕ, IsPrincipalSymmetric (I ^ n), ∃ m : ℕ, ∀ n ≥ m, IsPrincipalSymmetric (I ^ n),
    minGenSize I = 1].TFAE := by
  tfae_have 1 -> 2 := by
    intro h
    use 0
    simp [h]
  tfae_have 2 -> 3 := by
    simp only [ge_iff_le, mgs_eq_one_iff_kSymmetric (isSymmetric_of_isPSI hIp) hIB,
      forall_exists_index]
    intro m h
    obtain ⟨p, hp, hpI⟩ := exists_homog_eq_symmSpan_of_isPSI hI hIp
    suffices kSymmetric p by use p
    specialize h (max m (Nat.card α).factorial) (le_max_left _ _)
    apply mgs_le_factorial_of_isPSI at h
    contrapose! h
    have hn := lt_mgs_pow (max m (Nat.card α).factorial) hIB hpI hp h
    omega
  tfae_have 3 -> 1 := pow_isPSI_of_mgs_one (isSymmetric_of_isPSI hIp)
  tfae_finish


theorem pow_isPSI_tfae' {p : MvPolynomial α R} {i : ℕ} (hp : p.IsHomogeneous i) :
    [∀ n, IsPrincipalSymmetric ((symmSpan {p}) ^ n),
    ∃ m, ∀ n ≥ m, IsPrincipalSymmetric ((symmSpan {p}) ^ n),
    kSymmetric p].TFAE := by
  by_cases! hp0 : p = 0
  · simp [hp0]
  rw [← mgs_eq_one_iff_kSymmetric' hp hp0]
  exact pow_isPSI_tfae (isSingleDegGen_symmSpan hp) (by use p) <| symmSpan_eq_bot_iff.not.mpr hp0

theorem isPSI_mul_iff_mgs_eq_one {I J : Ideal (MvPolynomial (Fin 2) R)}
    (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
    (hIp : IsPrincipalSymmetric I) (hJp : IsPrincipalSymmetric J)
    (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) :
    IsPrincipalSymmetric (I * J) ↔ minGenSize I = 1 ∨ minGenSize J = 1 := by
  constructor
  · contrapose!
    intro ⟨hmI, hmJ⟩ hIJ
    apply mgs_le_factorial_of_isPSI at hIJ
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial_two] at hIJ
    suffices 3 ≤ minGenSize (I * J) by omega
    have hIp2 := hIp
    obtain ⟨p, hp, hIp⟩ := exists_homog_eq_symmSpan_of_isPSI hI hIp
    rw [hIp]
    apply le_trans ?_ (max_mgs_le_mgs_prod hp ?_ hJ hJB)
    · have := mgs_pos hJB
      omega
    · rw [ne_eq, mgs_eq_one_iff_kSymmetric (isSymmetric_of_isPSI hIp2) hIB] at hmI
      simp only [not_exists, not_and'] at hmI
      exact hmI p hIp
  · intro h
    wlog hmgs : minGenSize I = 1
    · rw [Or.comm] at h
      rw [mul_comm]
      refine this hJ hI hJp hIp hJB hIB h ?_
      simpa only [hmgs, or_false] using h
    · rw [mgs_eq_one_iff_kSymmetric (isSymmetric_of_isPSI hIp) hIB] at hmgs
      obtain ⟨p, hpk, hp⟩ := hmgs
      obtain ⟨q, hq⟩ := hJp
      rw [hp, hq, mul_symmSpan_of_kSymmetric hpk]
      use p * q

theorem isPSI_mul_iff_mgs_eq_one' {p q : MvPolynomial (Fin 2) R} {n m : ℕ}
    (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous m) :
    IsPrincipalSymmetric (symmSpan {p} * symmSpan {q}) ↔ kSymmetric p ∨ kSymmetric q := by
  by_cases! hp0 : p = 0
  · simp [hp0]
  by_cases! hq0 : q = 0
  · simp [hq0]
  rw [← mgs_eq_one_iff_kSymmetric' hp hp0, ← mgs_eq_one_iff_kSymmetric' hq hq0]
  refine isPSI_mul_iff_mgs_eq_one (isSingleDegGen_symmSpan hp) (isSingleDegGen_symmSpan hq)
    (by use p) (by use q) ?_ ?_
  · rwa [ne_eq, symmSpan_eq_bot_iff]
  · rwa [ne_eq, symmSpan_eq_bot_iff]


theorem isPSI_pow_tfae {I : Ideal (MvPolynomial (Fin 2) R)} (hI : IsSingleDegGen I)
    (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) :
    [∀ n, IsPrincipalSymmetric (I ^ n), IsPrincipalSymmetric (I ^ 2), minGenSize I = 1].TFAE := by
  tfae_have 1 -> 2 := fun h ↦ h 2
  tfae_have 2 -> 3 := by
    intro h
    rwa [pow_two, isPSI_mul_iff_mgs_eq_one hI hI hIp hIp hIB hIB, or_self] at h
  tfae_have 3 -> 1 := by
    intro h n
    induction n
    · simp
    · rename_i n ih
      rw [pow_succ, isPSI_mul_iff_mgs_eq_one (isSingleDegGen_pow hI n) hI ih hIp ?_ hIB]
      · right
        exact h
      · rw [← Submodule.zero_eq_bot] at hIB ⊢
        exact pow_ne_zero n hIB
  tfae_finish

theorem isPSI_pow_tfae' {p : MvPolynomial (Fin 2) R} {i : ℕ} (hp : p.IsHomogeneous i) :
    [∀ n, IsPrincipalSymmetric (symmSpan {p} ^ n), IsPrincipalSymmetric (symmSpan {p} ^ 2),
    kSymmetric p].TFAE := by
  by_cases! hp0 : p = 0
  · simp [hp0]
  rw [← mgs_eq_one_iff_kSymmetric' hp hp0]
  refine isPSI_pow_tfae (isSingleDegGen_symmSpan hp) (by use p) ?_
  rwa [ne_eq, symmSpan_eq_bot_iff]

end Field
