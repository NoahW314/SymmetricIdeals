import Mathlib
import SymmetricIdeals.Products.ProductMgs
import SymmetricIdeals.PsiObstructions
import Mathlib.Tactic.TFAE


variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

lemma symm_totalDegree (p : MvPolynomial α F) (σ : Equiv.Perm α) : p.totalDegree = (σ • p).totalDegree := by
  rw [symmAct_def, ← renameEquiv_apply, totalDegree_renameEquiv]

lemma C_mul_kSymmetric (p : MvPolynomial α F) (c : F) (h : kSymmetric p) : kSymmetric (C c * p) := by
  intro σ; obtain ⟨d, hp⟩ := h σ
  use d;
  rw [smul_mul', smul_eq_C_mul, hp, smul_eq_C_mul, symmAct_def, rename_C]
  ring

lemma symmSpan_kSymmetric {p : MvPolynomial α F} (h : kSymmetric p) :
  symmSpan {p} = Ideal.span {p} := by
    apply Submodule.span_eq_span
    intro q; simp only [mem_symmSet_singleton, Ideal.submodule_span_eq, SetLike.mem_coe,
      forall_exists_index]
    intro σ hq; obtain ⟨c, hc⟩ := h σ
    rw [← hq, hc, smul_eq_C_mul]
    apply Ideal.mul_mem_left; apply Ideal.subset_span; simp only [Set.mem_singleton_iff]
    intro q; simp only [Set.mem_singleton_iff, Ideal.submodule_span_eq, SetLike.mem_coe]
    intro hq; rw [hq]; apply Ideal.subset_span; exact mem_symmSet_singleton_self

lemma mgs_eq_one_iff_kSymmetric {I : Ideal (MvPolynomial α F)} (hI : IsSymmetricI I)
  (hIB : I ≠ ⊥) : min_gen_size I = 1 ↔ ∃ p, kSymmetric p ∧ I = symmSpan {p} := by
    constructor; intro h
    have hinf : {n | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S}.Nonempty := by
      contrapose! h; unfold min_gen_size;
      rw [h]; simp only [Nat.sInf_empty, ne_eq, zero_ne_one, not_false_eq_true]
    apply Nat.sInf_mem at hinf
    unfold min_gen_size at h; rw [h, Set.mem_setOf] at hinf
    obtain ⟨S, hS0, hS1, hSI⟩ := hinf
    rw [Finset.card_eq_one] at hS1; obtain ⟨p, hS1⟩ := hS1
    use p; rw [hS1, Finset.coe_singleton] at hSI
    suffices kSymmetric p by
      constructor; exact this
      rw [hSI]; symm
      exact symmSpan_kSymmetric this
    intro σ
    have hp0 : p ≠ 0 := by
      contrapose! hS0; rw [← hS0, hS1]
      exact Finset.mem_singleton.mpr rfl
    suffices p ∣ σ • p by
      obtain ⟨q, hq⟩ := this
      let hqd := hq; apply_fun totalDegree at hqd
      rw [totalDegree_mul_of_isDomain hp0, symm_totalDegree p σ] at hqd
      rw [Nat.left_eq_add, totalDegree_eq_zero_iff_eq_C] at hqd
      use (coeff 0 q)
      rw [smul_eq_C_mul, ← hqd, mul_comm, hq]

      contrapose! hp0
      rw [hp0, mul_zero] at hq
      exact (smul_eq_zero_iff_eq σ).mp hq
    rw [← Ideal.mem_span_singleton, ← hSI]
    apply hI σ
    rw [hSI]; apply Ideal.subset_span; rfl

    intro h
    obtain ⟨p, hp, hpI⟩ := h

    have hpS : 1 ∈ {n | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S} := by
      rw [Set.mem_setOf]
      use {p}; constructor; simp only [Finset.mem_singleton, ne_eq]
      contrapose! hIB; rw [hpI, ← hIB, symmSpan_zero]
      constructor; simp only [Finset.card_singleton]
      rw [hpI, symmSpan]; simp only [Finset.coe_singleton]
      exact symmSpan_kSymmetric hp
    apply antisymm (Nat.sInf_le hpS)
    apply le_csInf; use 1
    intro n hn; rw [Set.mem_setOf] at hn
    suffices n > 0 by exact this
    rw [gt_iff_lt, Nat.pos_iff_ne_zero]
    obtain ⟨S, hS0, hSn, hS⟩ := hn
    contrapose! hIB
    rw [hS, Ideal.span_eq_bot]; rw [hIB] at hSn
    simp only [Finset.card_eq_zero] at hSn
    simp only [hSn, Finset.coe_empty, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]


variable [DecidableEq α]

lemma mgs_eq_one_iff_kSymmetric' {p : MvPolynomial α F} {n : ℕ} (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) :
  min_gen_size (symmSpan {p}) = 1 ↔ kSymmetric p := by
    have hps : IsPrincipalSymmetric (symmSpan {p}) := by use p;
    apply psi_is_symm at hps
    have hpb : symmSpan {p} ≠ ⊥ := by rw [ne_eq, symmSpan_bot_iff]; exact hp0
    rw [mgs_eq_one_iff_kSymmetric hps hpb]
    constructor; swap; intro h; use p

    intro h;
    obtain ⟨q, hq, hpq⟩ := h
    have hr : q ∣ p := by
      rw [← Ideal.mem_span_singleton, ← symmSpan_kSymmetric hq, ← hpq]
      exact mem_symmSpan_self
    let hqp := hr
    obtain ⟨r, hr⟩ := hr;
    let hpqr0 := hp0; rw [hr, mul_ne_zero_iff] at hpqr0
    obtain ⟨hq0, hr0⟩ := hpqr0

    let hq2 := hq
    apply symmSpan_pmul_dvd hr at hq
    rw [hpq] at hq
    apply_fun minDeg at hq
    have hqh : q.IsHomogeneous q.totalDegree := by exact homogeneous_of_dvd_homogeneous hp hp0 hqp
    have hrh : r.IsHomogeneous r.totalDegree := by
      apply homogeneous_of_dvd_homogeneous  hp hp0
      use q; rw [mul_comm]; exact hr
    rw [minDeg_symmSpan hqh hq0, minDeg_pmul (singleDegGen_of_symmSpan hrh) hqh ?_ hq0] at hq
    rw [Nat.left_eq_add, minDeg_symmSpan hrh hr0, totalDegree_eq_zero_iff_eq_C] at hq
    rw [hr, hq, mul_comm]
    exact C_mul_kSymmetric q (coeff 0 r) hq2
    rw [ne_eq, symmSpan_bot_iff]; exact hr0

omit [DecidableEq α] in
@[simp] lemma power_bot_psi : ∀ n, IsPrincipalSymmetric ((⊥ : Ideal (MvPolynomial α F)) ^ n) := by
  intro n
  by_cases hn : n = 0
  simp only [hn, pow_zero, Ideal.one_eq_top, top_is_psi]
  rw [← Ideal.zero_eq_bot, zero_pow hn]
  exact bot_is_psi

omit [DecidableEq α] in
lemma power_psi_of_mgs_one {I : Ideal (MvPolynomial α F)} (hI : IsSymmetricI I) (h : min_gen_size I = 1) :
  ∀ n, IsPrincipalSymmetric (I^n) := by
    by_cases hIB : I = ⊥
    rw [hIB]; exact power_bot_psi

    intro n
    rw [mgs_eq_one_iff_kSymmetric hI hIB] at h
    obtain ⟨p, hp, hpI⟩ := h
    rw [hpI, powerPsi_of_kSymmetric hp]
    use p^n

theorem power_monomial_psi {I : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I)
  (hIm : ∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : F)) '' S))
  (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) : [∀ n : ℕ, IsPrincipalSymmetric (I^n),
  IsPrincipalSymmetric (I^2), min_gen_size I = 1].TFAE := by
    tfae_have 1 -> 2 := by intro h; specialize h 2; exact h
    tfae_have 2 -> 3 := by
      intro h
      rw [pow_two, monomialProduct_Psi hIm hIm hIp hIp hI hI hIB hIB] at h
      obtain ⟨d, h⟩ := h
      rw [or_self] at h
      rw [h.2, mgs_eq_one_iff_kSymmetric' (isHomogeneous_monomial 1 rfl)]
      exact h.1
      rw [ne_eq, monomial_eq_zero]; exact one_ne_zero
    tfae_have 3 -> 1 := by exact power_psi_of_mgs_one (psi_is_symm hIp)
    tfae_finish

theorem power_monomial_psi' {d : α →₀ ℕ} : [∀ n, IsPrincipalSymmetric ((symmSpan {monomial d (1 : F)})^n),
  IsPrincipalSymmetric ((symmSpan {monomial d (1 : F)})^2), kSymmetric (monomial d (1 : F))].TFAE := by
    rw [← mgs_eq_one_iff_kSymmetric' (isHomogeneous_monomial 1 rfl)]
    apply power_monomial_psi
    apply singleDegGen_of_symmSpan (isHomogeneous_monomial 1 rfl)
    use Set.range (fun σ : Equiv.Perm α => Finsupp.mapDomain σ d)
    unfold symmSpan; congr;
    ext e; simp only [mem_symmSet_singleton, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, symmAct_def, rename_monomial]
    use (monomial d 1)
    rw [ne_eq, symmSpan_bot_iff, monomial_eq_zero]; exact one_ne_zero
    rw [ne_eq, monomial_eq_zero]; exact one_ne_zero

lemma singleDegGen_power {I : Ideal (MvPolynomial α F)} (h : IsSingleDegGen I) :
  ∀ n, IsSingleDegGen (I^n) := by
    intro n
    induction' n with n ih
    simp only [IsSingleDegGen, pow_zero, Ideal.one_eq_top, minDeg_top]
    symm
    rw [Ideal.eq_top_iff_one]
    apply Ideal.subset_span
    simp only [homogeneousSubmoduleI, Submodule.restrictScalars_top, le_top, inf_of_le_left,
      SetLike.mem_coe, mem_homogeneousSubmodule]
    exact isHomogeneous_one α F

    rw [pow_succ]
    apply singleDegGen_mul ih h

variable [Finite α]

theorem power_psi {I : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I) (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) :
  [∀ n : ℕ, IsPrincipalSymmetric (I^n), ∃ m : ℕ, ∀ n ≥ m, IsPrincipalSymmetric (I^n),
  min_gen_size I = 1].TFAE := by
    tfae_have 1 -> 2 := by
      intro h; use 0; simp only [ge_iff_le, zero_le, forall_const]
      exact h
    tfae_have 2 -> 3 := by
      rw [mgs_eq_one_iff_kSymmetric (psi_is_symm hIp) hIB]
      contrapose; intro h; push_neg
      simp only [not_exists, not_and'] at h
      obtain ⟨p, hp, hpI⟩ := psi_homo_gen_of_singleDegGen hI hIp
      specialize h p hpI

      have hn : ∀ n, n < min_gen_size (I^n) := by
        intro n
        induction' n with n ih
        simp only [pow_zero, Ideal.one_eq_top, mgs_top, zero_lt_one]

        rw [pow_succ]
        suffices min_gen_size (I^n) + 1 ≤ min_gen_size (I^n * I) by
          calc n+1
            _ < min_gen_size (I^n) + 1 := by exact Nat.add_le_add_right ih 1
            _ ≤ min_gen_size (I^n * I) := this
        nth_rw 3 [hpI]; rw [mul_comm]
        apply max_mgs_le_mgs_prod hp h (singleDegGen_power hI n)
        rw [← Ideal.zero_eq_bot]; rw [← Ideal.zero_eq_bot] at hIB
        exact pow_ne_zero n hIB
      intro m; use (max m (Nat.card α).factorial); constructor
      apply le_max_left
      intro hpI
      apply psi_mgs_factorial at hpI
      specialize hn (max m (Nat.card α).factorial)
      apply lt_of_lt_of_le hn at hpI
      have hpI2 : (Nat.card α).factorial ≤ (max m (Nat.card α).factorial) := by apply le_max_right
      apply lt_of_lt_of_le hpI at hpI2
      rw [lt_self_iff_false] at hpI2
      exact hpI2
    tfae_have 3 -> 1 := by exact power_psi_of_mgs_one (psi_is_symm hIp)
    tfae_finish


theorem power_psi' {p : MvPolynomial α F} {i : ℕ} (hp : p.IsHomogeneous i) :
  [∀ n, IsPrincipalSymmetric ((symmSpan {p})^n), ∃ m, ∀ n ≥ m, IsPrincipalSymmetric ((symmSpan {p})^n),
  kSymmetric p].TFAE := by
    by_cases hp0 : p = 0
    simp only [hp0, symmSpan_zero, power_bot_psi, implies_true, ge_iff_le, exists_const,
      kSymmetric_zero, List.tfae_cons_self, List.tfae_singleton]

    rw [← mgs_eq_one_iff_kSymmetric' hp hp0]
    apply power_psi
    apply singleDegGen_of_symmSpan hp
    use p
    exact symmSpan_bot_iff.not.mpr hp0

theorem product_psi_two_vars {I J : Ideal (MvPolynomial (Fin 2) F)} (hI : IsSingleDegGen I)
  (hJ : IsSingleDegGen J) (hIp : IsPrincipalSymmetric I) (hJp : IsPrincipalSymmetric J) (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) :
  IsPrincipalSymmetric (I*J) ↔ min_gen_size I = 1 ∨ min_gen_size J = 1 := by
    constructor; contrapose!; intro h hIJ
    apply psi_mgs_factorial at hIJ
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial_two] at hIJ
    suffices 3 ≤ min_gen_size (I*J) by omega
    obtain ⟨hmI, hmJ⟩ := h; let hIp2 := hIp
    obtain ⟨p, hp, hIp⟩ := psi_homo_gen_of_singleDegGen hI hIp; rw [hIp]
    apply le_trans ?_ (max_mgs_le_mgs_prod hp ?_ hJ hJB)
    suffices 2 ≤ min_gen_size J by omega
    contrapose! hmJ
    let hmJ0 := mgs_pos hJB
    omega

    rw [ne_eq, mgs_eq_one_iff_kSymmetric (psi_is_symm hIp2) hIB] at hmI
    simp only [not_exists, not_and'] at hmI
    exact hmI p hIp


    intro h
    wlog hmgs : min_gen_size I = 1
    rw [Or.comm] at h; rw [mul_comm]
    apply this hJ hI hJp hIp hJB hIB h
    simp only [hmgs, or_false] at h; exact h

    rw [mgs_eq_one_iff_kSymmetric (psi_is_symm hIp) hIB] at hmgs
    obtain ⟨p, hpk, hp⟩ := hmgs
    obtain ⟨q, hq⟩ := hJp
    rw [hp, hq, productPsi_of_kSymmetric hpk]
    use p*q

theorem product_psi_two_vars' {p q : MvPolynomial (Fin 2) F} {n m : ℕ} (hp : p.IsHomogeneous n)
  (hq : q.IsHomogeneous m) :
  IsPrincipalSymmetric ((symmSpan {p})*(symmSpan {q})) ↔ kSymmetric p ∨ kSymmetric q := by
    by_cases hp0 : p = 0
    simp only [hp0, symmSpan_zero, Submodule.bot_mul, bot_is_psi, kSymmetric_zero, true_or]

    by_cases hq0 : q = 0
    simp only [hq0, symmSpan_zero, Submodule.mul_bot, bot_is_psi, kSymmetric_zero, or_true]

    rw [← mgs_eq_one_iff_kSymmetric' hp hp0, ← mgs_eq_one_iff_kSymmetric' hq hq0]
    apply product_psi_two_vars (singleDegGen_of_symmSpan hp) (singleDegGen_of_symmSpan hq)
    use p; use q
    rw [ne_eq, symmSpan_bot_iff]; exact hp0
    rw [ne_eq, symmSpan_bot_iff]; exact hq0


theorem power_psi_two_vars {I : Ideal (MvPolynomial (Fin 2) F)} (hI : IsSingleDegGen I)
  (hIp : IsPrincipalSymmetric I) (hIB : I ≠ ⊥) : [∀ n, IsPrincipalSymmetric (I^n), IsPrincipalSymmetric (I^2),
  min_gen_size I = 1].TFAE := by
    tfae_have 1 -> 2 := by intro h; specialize h 2; exact h
    tfae_have 2 -> 3 := by
      intro h; rw [pow_two] at h
      rw [product_psi_two_vars hI hI hIp hIp hIB hIB, or_self] at h
      exact h
    tfae_have 3 -> 1 := by
      intro h; intro n
      induction' n with n ih
      simp only [pow_zero, Ideal.one_eq_top, top_is_psi]
      rw [pow_succ, product_psi_two_vars]
      right; exact h
      exact singleDegGen_power hI n
      exact hI; exact ih; exact hIp
      rw [← Submodule.zero_eq_bot]; rw [← Submodule.zero_eq_bot] at hIB
      exact pow_ne_zero n hIB; exact hIB
    tfae_finish

theorem power_psi_two_vars' {p : MvPolynomial (Fin 2) F} {i : ℕ} (hp : p.IsHomogeneous i) :
  [∀ n, IsPrincipalSymmetric ((symmSpan {p})^n), IsPrincipalSymmetric ((symmSpan {p})^2),
  kSymmetric p].TFAE := by
    by_cases hp0 : p = 0
    simp only [hp0, symmSpan_zero, power_bot_psi, implies_true, kSymmetric_zero,
      List.tfae_cons_self, List.tfae_singleton]

    rw [← mgs_eq_one_iff_kSymmetric' hp hp0]
    apply power_psi_two_vars (singleDegGen_of_symmSpan hp)
    use p; rw [ne_eq, symmSpan_bot_iff]; exact hp0
