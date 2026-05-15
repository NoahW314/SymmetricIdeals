/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.MinimalGenerating
import SymmetricIdeals.SingleDegGen
import SymmetricIdeals.GradedMinimalGenerators
import SymmetricIdeals.OrderType
import SymmetricIdeals.Products.kSymmetric
import SymmetricIdeals.Products.Monomial
import SymmetricIdeals.SubmoduleSMul
import SymmetricIdeals.Degree

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

open MvPolynomial Rename Equiv
attribute [local instance] MvPolynomial.gradedAlgebra


lemma dvd_iff_perm_dvd {p q : MvPolynomial α R} (σ : Equiv.Perm α) : p ∣ q ↔ σ • p ∣ σ • q := by
  constructor
  · intro ⟨r, h⟩
    use σ • r
    rw [h, smul_mul']
  · intro ⟨r, h⟩
    use σ⁻¹ • r
    apply_fun (σ⁻¹ • ·) at h
    rwa [smul_mul', inv_smul_smul, inv_smul_smul] at h

lemma perm_mem_symmSet' {p q : MvPolynomial α R} (σ : Equiv.Perm α) [Fintype (symmSet {p})]
    (h : q ∈ (symmSet {p}).toFinset.val) : σ • q ∈ (symmSet {p}).toFinset.val := by
  simp_all


section IsDomain

variable {α R : Type*} [CommRing R] [IsDomain R] {I : Ideal (MvPolynomial α R)}

lemma homogSubI_pmul {p : MvPolynomial α R} {I : Ideal (MvPolynomial α R)} {n : ℕ}
    (hp : p.IsHomogeneous n) (hI : IsSingleDegGen I) :
    homogeneousSubmoduleI (minDeg (pmul p I)) (pmul p I) =
    pmul p (homogeneousSubmoduleI (minDeg I) I) := by
  by_cases! hIB : I = ⊥
  · simp [hIB]
  by_cases! hp0 : p = 0
  · simp [hp0, pmul]
  ext q
  simp only [Submodule.mem_inf, mem_homogeneousSubmodule, Submodule.restrictScalars_mem, pmul_inf,
    pmul_restrictScalars, and_congr_left_iff]
  intro hqI
  constructor
  · intro hq
    by_cases hq0 : q = 0
    · simp [hq0]
    simp only [Submodule.mem_map, LinearMap.mulLeft_apply, mem_homogeneousSubmodule] at hqI ⊢
    obtain ⟨r, hrI, hr⟩ := hqI
    use r
    constructor
    · rw [minDeg_pmul hI hp hIB hp0] at hq
      have hrq : r ∣ q := by
        rw [← hr]
        exact dvd_mul_left r p
      have hrh := isHomogeneous_of_dvd_isHomogeneous hq hq0 hrq
      suffices r.totalDegree = minDeg I by rwa [← this]
      apply IsHomogeneous.mul hp at hrh
      rw [hr] at hrh
      apply IsHomogeneous.inj_right hrh hq at hq0
      exact Nat.add_left_cancel hq0
    · exact hr
  · intro hq
    simp only [Submodule.mem_map, mem_homogeneousSubmodule, LinearMap.mulLeft_apply] at hq
    obtain ⟨r, hr, hq⟩ := hq
    rw [minDeg_pmul hI hp hIB hp0, ← hq]
    exact IsHomogeneous.mul hp hr

lemma pmul_isSingleDegGen_iff {p : MvPolynomial α R} {I : Ideal (MvPolynomial α R)} {n : ℕ}
    (hp0 : p ≠ 0) (hp : p.IsHomogeneous n) : IsSingleDegGen (pmul p I) ↔ IsSingleDegGen I := by
  constructor
  · intro h
    rw [isSingleDegGen_iff] at h ⊢
    obtain ⟨m, S, hS, h⟩ := h
    use m - n
    have hSp : ∀ g ∈ S, ∃ q, g = p * q := by
      intro g hg
      apply Ideal.subset_span at hg
      simp only [← h, Submodule.map_coe, LinearMap.mulLeft_apply, Set.mem_image,
        SetLike.mem_coe] at hg
      obtain ⟨q, _, hg⟩ := hg
      use q
      exact hg.symm
    use Set.range (fun g : S => Classical.choose (hSp g.1 g.2))
    constructor
    · intro q
      simp only [Set.mem_range, Subtype.exists, SetLike.mem_coe, mem_homogeneousSubmodule,
        forall_exists_index]
      intro g hg hgq
      have hgq : g = p * q := by
        rw [← hgq]
        exact Classical.choose_spec (hSp g hg)
      by_cases hq0 : q = 0
      · simp [hq0, isHomogeneous_zero]
      have hg0 : g ≠ 0 := by simp [*]
      apply hS at hg
      simp only [SetLike.mem_coe, mem_homogeneousSubmodule] at hg
      have hq := isHomogeneous_of_dvd_isHomogeneous hg hg0 <| Dvd.intro_left p hgq.symm
      suffices q.totalDegree = m - n by rwa [← this]
      apply IsHomogeneous.mul hp at hq
      rw [← hgq] at hq
      apply IsHomogeneous.inj_right hg hq at hg0
      exact Nat.eq_sub_of_add_eq' hg0.symm
    · refine Ideal.span_singleton_mul_right_injective hp0 ?_
      simp only [← pmul_eq_span_mul, Ideal.span_mul_span, h]
      congr
      ext g
      simp only [Set.singleton_mul, Set.mem_image, Set.mem_range, Subtype.exists]
      constructor
      · intro hg
        specialize hSp g hg
        use Classical.choose hSp
        constructor
        · use g, hg
        · exact (Classical.choose_spec hSp).symm
      · intro ⟨q, ⟨g', ⟨hg', hq⟩⟩, h'⟩
        have hgq : g' = p * q := by
          rw [← hq]
          exact Classical.choose_spec (hSp g' hg')
        rwa [← h', ← hgq]
  · unfold IsSingleDegGen
    intro h
    nth_rw 1 [h]
    simp [homogSubI_pmul hp h, pmul, LinearMap.map_span]

end IsDomain

section Field

variable {α R : Type*} [Field R]

noncomputable scoped
instance MvPolynomial.normalizedGCDMonoid : NormalizedGCDMonoid (MvPolynomial α R) := by
  have : NormalizationMonoid (MvPolynomial α R) := UniqueFactorizationMonoid.normalizationMonoid
  exact UniqueFactorizationMonoid.toNormalizedGCDMonoid (MvPolynomial α R)

lemma gcd_symmSet_kSymmetric {p : MvPolynomial α R} [Fintype (symmSet {p})] :
    kSymmetric ((symmSet {p}).toFinset).val.gcd := by
  intro σ
  suffices Associated ((symmSet {p}).toFinset).val.gcd (σ • ((symmSet {p}).toFinset).val.gcd) by
    obtain ⟨u, hu⟩ := this
    rw [mul_comm] at hu
    obtain ⟨c, hcu, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp <| Units.isUnit u
    use c
    simp [hc, ← hu, smul_eq_C_mul]
  rw [← dvd_dvd_iff_associated]
  constructor
  · rw [dvd_iff_perm_dvd σ⁻¹, inv_smul_smul, Multiset.dvd_gcd]
    intro b hb
    rw [dvd_iff_perm_dvd σ, smul_inv_smul]
    exact Multiset.gcd_dvd <| perm_mem_symmSet' σ hb
  · rw [Multiset.dvd_gcd]
    intro b hb
    rw [dvd_iff_perm_dvd σ⁻¹, inv_smul_smul]
    exact Multiset.gcd_dvd <| perm_mem_symmSet' σ⁻¹ hb

variable [Finite α]

lemma mgs_pmul_eq_mgs (p : MvPolynomial α R) {I : Ideal (MvPolynomial α R)} {n : ℕ}
    (hI : IsSingleDegGen I) (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) :
    minGenSize (pmul p I) = minGenSize I := by
  have hpI := (pmul_isSingleDegGen_iff hp0 hp).mpr hI
  rw [mgs_eq_finrank hpI, mgs_eq_finrank hI, homogSubI_pmul hp hI, ← rank_eq_pmul_rank p hp0]


lemma mgs_one_le_mgs_mul' {J : Ideal (MvPolynomial α R)} {p : MvPolynomial α R} {n : ℕ}
    (σ : Equiv.Perm α) (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) (hp0 : p ≠ 0)
    (h : Module.finrank R (pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)) -
      Module.finrank R ((pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)) ⊓
        (pmul p (homogeneousSubmoduleI (minDeg J) J)) : Submodule R (MvPolynomial α R)) ≥ 1) :
    minGenSize J + 1 ≤ minGenSize ((symmSpan {p}) * J) := by
  rw [mgs_eq_finrank hJ, mgs_eq_finrank (isSingleDegGen_mul (isSingleDegGen_symmSpan hp) hJ)]
  let U := homogeneousSubmoduleI (minDeg ((symmSpan {p}) * J)) ((symmSpan {p}) * J)
  let V := pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)
  let W := pmul p (homogeneousSubmoduleI (minDeg J) J)
  have hU : Module.Finite R U := homogSubI_mod_fin _ _
  have hV : Module.Finite R V := by
    unfold V
    rw [← homogSubI_pmul (perm_isHomogeneous σ hp) hJ]
    exact homogSubI_mod_fin _ _
  have hW : Module.Finite R W := by
    unfold W
    rw [← homogSubI_pmul hp hJ]
    exact homogSubI_mod_fin _ _
  calc Module.finrank R U
    _ ≥ Module.finrank R (V ⊔ W : Submodule R (MvPolynomial α R)) := by
      apply Submodule.finrank_mono
      unfold U V W
      refine sup_le ?_ ?_
      · rw [← homogSubI_pmul (perm_isHomogeneous σ hp) hJ,
          minDeg_pmul_perm_eq_minDeg_symmSpan σ hJ hp]
        exact homogSubI_monotone (minDeg (symmSpan {p} * J)) pmul_perm_le_symmSpan_mul
      · rw [← homogSubI_pmul hp hJ, minDeg_pmul_eq_minDeg_symmSpan hJ hp]
        exact homogSubI_monotone (minDeg (symmSpan {p} * J)) pmul_le_symmSpan_mul
    _ = Module.finrank R V + Module.finrank R W -
        Module.finrank R (V ⊓ W : Submodule R (MvPolynomial α R)) := by
      simp only [← Submodule.finrank_sup_add_finrank_inf_eq V W, add_tsub_cancel_right]
    _ = Module.finrank R W + (Module.finrank R V -
        Module.finrank R (V ⊓ W : Submodule R (MvPolynomial α R))) := by
      rw [← Nat.add_sub_assoc <| Submodule.finrank_mono inf_le_left, Nat.add_comm]
    _ ≥ Module.finrank R W + 1 := by
      rwa [ge_iff_le, add_le_add_iff_left (Module.finrank R W)]
    _ = Module.finrank R (homogeneousSubmoduleI (minDeg J) J) + 1 := by
      rw [← rank_eq_pmul_rank p hp0]

omit [Finite α] in
lemma isHomogeneous_totalDegree {p q r : MvPolynomial α R} {n : ℕ} (h : p = q * r)
    (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) : q.IsHomogeneous q.totalDegree :=
  isHomogeneous_of_dvd_isHomogeneous hp hp0 <| Dvd.intro r h.symm

omit [Finite α] in
lemma isHomogeneous_totalDegree' {p q r : MvPolynomial α R} {n : ℕ} (h : p = q * r)
    (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) : r.IsHomogeneous r.totalDegree :=
  isHomogeneous_of_dvd_isHomogeneous hp hp0 <| Dvd.intro_left q h.symm


omit [Finite α] in
private lemma aux_span_eq_pmul_gcd_span [DecidableEq (MvPolynomial α R)]
    (s : Finset (MvPolynomial α R)) :
    Ideal.span s = pmul (s.val.gcd) (Ideal.span (SetLike.coe (Finset.image
    (fun g : s ↦ Classical.choose (Multiset.gcd_dvd g.2)) Finset.univ))) := by
  rw [pmul, LinearMap.map_span]
  congr
  ext g
  constructor
  · intro hg
    have hg : g ∈ s := by simpa using hg
    simp only [Set.mem_image, SetLike.mem_coe]
    let hgcd := Multiset.gcd_dvd hg
    use Classical.choose hgcd
    constructor
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      use ⟨g, hg⟩
    · exact (Classical.choose_spec hgcd).symm
  · intro hgS'
    rw [Set.mem_image] at hgS'
    obtain ⟨g', hgS', hgg⟩ := hgS'
    simp_rw [SetLike.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hgS'
    obtain ⟨⟨g₁, hg₁⟩, hgg₁⟩ := hgS'
    have hSgg₁ : s.val.gcd * g' = g₁ := by
      rw [← hgg₁]
      exact (Classical.choose_spec (Multiset.gcd_dvd hg₁)).symm
    simpa [← hgg, hSgg₁] using hg₁

theorem max_mgs_le_mgs_prod {p : MvPolynomial α R} {n : ℕ} {J : Ideal (MvPolynomial α R)}
    (hp : p.IsHomogeneous n) (hpk : ¬ kSymmetric p) (hJ : IsSingleDegGen J) (hJB : J ≠ ⊥) :
    minGenSize J + 1 ≤ minGenSize ((symmSpan {p}) * J) := by
  have : Fintype (symmSet {p}) := Fintype.ofFinite ↑(⋃ σ, (fun x ↦ σ • x) '' {p})
  let q := ((symmSet {p}).toFinset).val.gcd
  have hpq : q ∣ p := by simp [q, Multiset.gcd_dvd]
  obtain ⟨p', hpq⟩ := hpq
  have hp0 : p ≠ 0 := by
    contrapose! hpk
    simp [hpk]
  have hp'h := isHomogeneous_totalDegree' hpq hp hp0
  have hqh := isHomogeneous_totalDegree hpq hp hp0
  have hq : kSymmetric q := gcd_symmSet_kSymmetric
  rw [hpq, mul_ne_zero_iff] at hp0
  obtain ⟨hq0, hp0'⟩ := hp0
  obtain ⟨r, σ, hr, hrp', hrσ⟩ : ∃ r, ∃ σ : Equiv.Perm α, Prime r ∧ r ∣ p' ∧ ¬r ∣ σ • p' := by
    obtain ⟨r, hr⟩ : ∃ r, Prime r ∧ r ∣ p' := by
      simp only [← irreducible_iff_prime]
      refine WfDvdMonoid.exists_irreducible_factor ?_ hp0'
      rw [isUnit_iff_eq_C_of_isReduced]
      contrapose! hpk
      obtain ⟨r, hr, hrp'⟩ := hpk
      rw [hpq, hrp']
      exact kSymmetric_C_mul' r hq
    use r
    by_contra! hσ
    simp only [hr, forall_const] at hσ
    suffices q * r ∣ q by exact hr.1.not_unit <| (mul_dvd_left_iff_isUnit hq0).mp this
    rw [Multiset.dvd_gcd]
    intro b hb
    simp only [Finset.mem_val, Set.mem_toFinset, mem_symmSet_singleton] at hb
    obtain ⟨σ, hb⟩ := hb
    rw [← hb, hpq, smul_mul']
    obtain ⟨a, ha⟩ := hσ σ
    obtain ⟨c, hq⟩ := hq σ
    use C c * a
    rw [ha, hq, smul_eq_C_mul]
    ring
  have hprJ : minGenSize (symmSpan {p} * J) = minGenSize (symmSpan {p'} * J) := by
    rw [mgs_eq_finrank (isSingleDegGen_mul (isSingleDegGen_symmSpan hp'h) hJ),
      mgs_eq_finrank (isSingleDegGen_mul (isSingleDegGen_symmSpan hp) hJ)]
    nth_rw 2 [rank_eq_pmul_rank q hq0]
    rw [← homogSubI_pmul hqh (isSingleDegGen_mul (isSingleDegGen_symmSpan hp'h) hJ), pmul_mul,
      symmSpan_eq_pmul_symmSpan hpq hq]
  rw [hprJ]
  obtain ⟨T, hT, hTJ⟩ := isSingleDegGen_iff_exists_finset.mp hJ
  classical
  rw [← Ideal.span_sdiff_singleton_zero'] at hTJ
  have hTe' : ∃ x ∈ (T \ {0}), x ≠ 0 := by
    contrapose! hJB
    simpa [hTJ] using hJB
  let f := (T \ {0}).val.gcd
  have hf0 : f ≠ 0 := by
    simpa only [f, ne_eq, Multiset.gcd_eq_zero_iff, not_forall, exists_prop,
      Finset.mem_val] using hTe'
  have hfh : f.IsHomogeneous f.totalDegree := by
    obtain ⟨g, hg, hg0⟩ := hTe'
    refine isHomogeneous_of_dvd_isHomogeneous (n := minDeg J) (hT ?_) hg0 (Multiset.gcd_dvd hg)
    simpa [hg0] using hg
  let S' := Finset.image (fun g : (T \ {0} : Finset (MvPolynomial α R)) ↦
    Classical.choose (Multiset.gcd_dvd g.2)) Finset.univ
  have hJS : J = pmul f (Ideal.span S') := by
    rw [hTJ]
    exact aux_span_eq_pmul_gcd_span (T \ {0})
  have hS's : IsSingleDegGen (Ideal.span (SetLike.coe S')) := by
    rwa [← pmul_isSingleDegGen_iff hf0 hfh, ← hJS]
  rw [hJS, mgs_pmul_eq_mgs f hS's hfh hf0, mul_comm, ← pmul_mul, mul_comm,
      mgs_pmul_eq_mgs f (isSingleDegGen_mul (isSingleDegGen_symmSpan hp'h) hS's) hfh hf0]
  obtain ⟨T', hT', hJT'⟩ := isSingleDegGen_iff_exists_finset.mp hS's
  nth_rw 2 [← Ideal.span_sdiff_singleton_zero'] at hJT'
  have hT'g : ∃ g ∈ T' \ {0}, ¬ r ∣ g  := by
    have hSu : IsUnit (S'.val.gcd) := by
      rw [← mul_dvd_left_iff_isUnit hf0, Multiset.dvd_gcd]
      intro f' hf'
      rw [Finset.mem_val] at hf'
      have hgS' : (Classical.choose (Multiset.gcd_dvd hf')) ∈ S' := by
        simp only [S', Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
          Subtype.exists]
        use f', hf'
      obtain ⟨g', hfg'⟩ := Multiset.gcd_dvd hgS'
      rw [Classical.choose_spec <| Multiset.gcd_dvd hf', hfg', ← mul_assoc]
      exact dvd_mul_right (f * S'.val.gcd) g'
    apply Prime.not_unit at hr
    contrapose! hr
    refine isUnit_of_dvd_unit ?_ hSu
    simp only [Multiset.dvd_gcd, Finset.mem_val]
    intro g hg
    have hgT' : g ∈ Ideal.span (T' \ {0} : Finset (MvPolynomial α R)) := by
      rw [← hJT']
      exact Submodule.mem_span_of_mem hg
    refine dvd_of_mem_span ?_ hgT'
    simpa using hr
  refine mgs_one_le_mgs_mul' σ hS's hp'h hp0' ?_
  contrapose! hT'g
  rw [Nat.lt_one_iff] at hT'g
  apply Nat.le_of_sub_eq_zero at hT'g
  let M := (homogeneousSubmoduleI (minDeg (Ideal.span (SetLike.coe S')))
    (Ideal.span (SetLike.coe S')))
  have hminf : Module.Finite R (pmul (σ • p') M) := by
    rw [← homogSubI_pmul (perm_isHomogeneous σ hp'h) hS's]
    exact homogSubI_mod_fin _ _
  intro g hgS
  have hg : (σ • p') * g ∈ pmul (σ • p') M := by
    refine mem_pmul_of_mul_mem _ _ ?_
    unfold M
    rw [homogeneousSubmoduleI, Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · refine hT' ?_
      rw [Finset.mem_coe]
      exact Finset.sdiff_subset hgS
    · rw [hJT']
      refine Submodule.mem_span_of_mem ?_
      simpa using hgS
  have hrg : p' ∣ (σ • p') * g := by
    rw [← Submodule.eq_of_le_of_finrank_le inf_le_left hT'g, Submodule.mem_inf] at hg
    exact dvd_of_mem_pmul hg.2
  apply dvd_trans hrp' at hrg
  apply hr.dvd_or_dvd at hrg
  tauto

theorem max_mgs_le_mgs_prod_psi {p q : MvPolynomial α R} {n m : ℕ} (hp : p.IsHomogeneous n)
    (hq : q.IsHomogeneous m) (hpk : ¬ kSymmetric p) (hqk : ¬ kSymmetric q) :
    max (minGenSize (symmSpan {p})) (minGenSize (symmSpan {q})) + 1 ≤
    minGenSize ((symmSpan {p}) * (symmSpan {q})) := by
  refine Nat.add_le_of_le_sub ?_ ?_
  · refine mgs_pos <| mul_ne_zero ?_ ?_
    · contrapose! hpk
      rw [symmSpan, Ideal.zero_eq_bot, Ideal.span_eq_bot] at hpk
      simp [hpk p mem_symmSet_singleton_self]
    · contrapose! hqk
      rw [symmSpan, Ideal.zero_eq_bot, Ideal.span_eq_bot] at hqk
      simp [hqk q mem_symmSet_singleton_self]
  · refine max_le ?_ ?_
    · refine Nat.le_sub_of_add_le ?_
      rw [mul_comm]
      apply max_mgs_le_mgs_prod hq hqk (isSingleDegGen_symmSpan hp)
        (symmSpan_ne_bot_of_not_kSymmetric hpk)
    · exact Nat.le_sub_of_add_le <| max_mgs_le_mgs_prod hp hpk (isSingleDegGen_symmSpan hq)
        (symmSpan_ne_bot_of_not_kSymmetric hqk)


end Field
