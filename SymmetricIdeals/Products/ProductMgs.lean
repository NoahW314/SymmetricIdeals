import Mathlib
import SymmetricIdeals.MinimalGenerating
import SymmetricIdeals.SingleDegGen
import SymmetricIdeals.GradedMinimalGenerators
import SymmetricIdeals.OrderType
import SymmetricIdeals.Products.kSymmetric
import SymmetricIdeals.Products.Monomial

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra




noncomputable
instance MvPolynomial.normalizedGCDMonoid : NormalizedGCDMonoid (MvPolynomial α F) := by
  have hnm : NormalizationMonoid (MvPolynomial α F) := UniqueFactorizationMonoid.normalizationMonoid
  apply UniqueFactorizationMonoid.toNormalizedGCDMonoid (MvPolynomial α F)


lemma perm_dvd {p q : MvPolynomial α F} (σ : Equiv.Perm α) : p ∣ q ↔ σ • p ∣ σ • q := by
  constructor; intro h;
  obtain ⟨r, h⟩ := h
  use σ • r
  rw [h, smul_mul']

  intro h
  obtain ⟨r, h⟩ := h
  use σ⁻¹ • r
  apply_fun (σ⁻¹ • .) at h
  rw [smul_mul', inv_smul_smul, inv_smul_smul] at h
  exact h

lemma perm_mem_symmSet {p q : MvPolynomial α F} (σ : Equiv.Perm α) [Fintype (symmSet {p})]
  (h : q ∈ (symmSet {p}).toFinset.val) : σ • q ∈ (symmSet {p}).toFinset.val := by
    simp only [Finset.mem_val, Set.mem_toFinset, mem_symmSet_singleton]
    simp only [Finset.mem_val, Set.mem_toFinset, mem_symmSet_singleton] at h
    obtain ⟨τ, hτ⟩ := h
    use (σ * τ); rw [← hτ, mul_smul]

lemma gcd_symmSet_kSymmetric {p : MvPolynomial α F} [Fintype (symmSet {p})] :
  kSymmetric ((symmSet {p}).toFinset).val.gcd := by
    intro σ; let q := ((symmSet {p}).toFinset).val.gcd
    suffices Associated q (σ • q) by
      obtain ⟨u, hu⟩ := this
      rw [mul_comm] at hu
      have huu : IsUnit u.1 := by exact Units.isUnit u
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at huu
      obtain ⟨c, hcu, hc⟩ := huu
      use c; rw [smul_eq_C_mul, ← hc]
      symm; exact hu
    rw [← dvd_dvd_iff_associated]
    constructor

    rw [perm_dvd σ⁻¹, inv_smul_smul, Multiset.dvd_gcd]
    intro b hb
    rw [perm_dvd σ, smul_inv_smul]
    apply Multiset.gcd_dvd
    exact perm_mem_symmSet σ hb

    rw [Multiset.dvd_gcd]; intro b hb
    rw [perm_dvd σ⁻¹, inv_smul_smul]
    apply Multiset.gcd_dvd
    exact perm_mem_symmSet σ⁻¹ hb

variable {R : Type*} [CommSemiring R] [Module R (MvPolynomial α F)]
noncomputable def pmul (p : MvPolynomial α F) (M : Submodule R (MvPolynomial α F))
  := Submodule.span R ((p * .) '' M)

lemma mem_pmul_of_mul_mem {q : MvPolynomial α F} (p : MvPolynomial α F) {M : Submodule R (MvPolynomial α F)}
  (hq : q ∈ M) : p*q ∈ pmul p M := by
    apply Submodule.subset_span
    simp only [Set.mem_image, SetLike.mem_coe]; use q

variable [SMulCommClass R (MvPolynomial α F) (MvPolynomial α F)]

lemma pmul_eq {p : MvPolynomial α F} {M : Submodule R (MvPolynomial α F)} :
  pmul p M = (p * .) '' M := by
    ext x; simp only [pmul, SetLike.mem_coe, Set.mem_image]
    constructor; intro h
    rw [Submodule.mem_span_image_iff_exists_fun] at h
    obtain ⟨T, hT, ⟨c, hc⟩⟩ := h
    use (∑ i, c i • i); constructor;
    apply Submodule.sum_mem; intro i hi
    apply Submodule.smul_mem; apply hT
    apply Subtype.coe_prop
    rw [← hc, Finset.mul_sum]
    apply Finset.sum_congr; rfl
    intro i hi
    rw [mul_smul_comm]

    intro h
    obtain ⟨y, hy, h⟩ := h
    rw [← h]
    exact mem_pmul_of_mul_mem p hy

@[simp] lemma pmul_zero {M : Submodule R (MvPolynomial α F)} : pmul 0 M = 0 := by
  rw [Submodule.zero_eq_bot, Submodule.eq_bot_iff]; intro x
  rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
  intro h; obtain ⟨y, h⟩ := h
  rw [← h.2, zero_mul]
@[simp] lemma pmul_bot {p : MvPolynomial α F} : pmul p (⊥ : Submodule R (MvPolynomial α F)) = 0 := by
  rw [Submodule.zero_eq_bot, Submodule.eq_bot_iff]; intro x
  rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
  simp only [Submodule.bot_coe, Set.mem_singleton_iff, exists_eq_left, mul_zero]
  intro h; symm; exact h

lemma pmul_bij (p : MvPolynomial α F) (M : Submodule R (MvPolynomial α F)) (hp : p ≠ 0) :
  Function.Bijective ((fun q => ⟨p*q, by apply mem_pmul_of_mul_mem; exact q.2⟩) : M → (pmul p M)) := by
    constructor
    intro m n hnm;
    simp only [Subtype.mk.injEq, mul_eq_mul_left_iff, SetLike.coe_eq_coe, hp, or_false] at hnm
    exact hnm

    intro q; simp only [Subtype.exists]
    have hq : q.1 ∈ (p * .) '' M := by rw [← pmul_eq]; simp only [Subtype.coe_prop]
    rw [Set.mem_image] at hq
    obtain ⟨a, ha, hq⟩ := hq
    use a; use ha
    simp only [hq, Subtype.coe_eta]

noncomputable def pmul_linear_map (p : MvPolynomial α F) (M : Submodule R (MvPolynomial α F)) :
  M →ₗ[R] (pmul p M) := ⟨⟨fun q => ⟨p*q, by
  apply mem_pmul_of_mul_mem; exact q.2
  ⟩, by
  simp only [Submodule.coe_add, mul_add, AddMemClass.mk_add_mk, implies_true]
  ⟩, by
  simp only [SetLike.val_smul, RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq,
    Subtype.forall]
  intro r m hm
  apply mul_smul_comm
  ⟩
noncomputable def pmul_equiv (p : MvPolynomial α F) (M : Submodule R (MvPolynomial α F)) (hp : p ≠ 0) :
  M ≃ₗ[R] (pmul p M) := LinearEquiv.ofBijective (pmul_linear_map p M) (pmul_bij p M hp)



lemma dvd_of_mem_pmul {p q : MvPolynomial α F} (M : Submodule F (MvPolynomial α F))
  (h : q ∈ pmul p M) : p ∣ q := by
    unfold pmul at h
    rw [Submodule.mem_span_iff_exists_finset_subset] at h
    obtain ⟨f, T, hT, hf, hq⟩ := h
    rw [← hq]
    apply Finset.dvd_sum
    intro t ht
    rw [smul_eq_C_mul]
    apply Dvd.dvd.mul_left ?_ (C (f t))
    apply hT at ht; simp only [Set.mem_image, SetLike.mem_coe] at ht
    obtain ⟨x, ht⟩ := ht
    use x; symm; exact ht.2

lemma rank_eq_pmul_rank (p : MvPolynomial α F) {M : Submodule R (MvPolynomial α F)} (hp : p ≠ 0) :
  Module.finrank R M = Module.finrank R (pmul p M) := by
    apply LinearEquiv.finrank_eq (pmul_equiv p M hp)

lemma pmul_span {p : MvPolynomial α F} {S : Set (MvPolynomial α F)} :
  pmul p (Submodule.span R S) = Submodule.span R ((p * .) '' S) := by
    ext q; constructor; intro hq
    have hq : q ∈ (p * .) '' (Submodule.span R S) := by
      rw [← pmul_eq]; simp only [SetLike.mem_coe]
      exact hq
    rw [Set.mem_image] at hq
    obtain ⟨r, hr, hq⟩ := hq
    rw [SetLike.mem_coe, Submodule.mem_span_iff_exists_finset_subset] at hr
    obtain ⟨f, T, hT, hf, hr⟩ := hr
    rw [← hq, ← hr, Finset.mul_sum]
    apply Submodule.sum_mem; intro t ht
    rw [mul_smul_comm]; apply Submodule.smul_mem
    apply Submodule.subset_span; rw [Set.mem_image]
    use t; constructor; apply hT; exact ht; rfl

    intro hq
    rw [Submodule.mem_span_image_iff_exists_fun] at hq
    obtain ⟨T, hT, f, hq⟩ := hq
    rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
    use (∑ i, f i • i); constructor
    rw [SetLike.mem_coe]; apply Submodule.sum_mem
    intro i hi; apply Submodule.smul_mem
    apply Submodule.subset_span; apply hT i.2

    rw [← hq, Finset.mul_sum]
    apply Finset.sum_congr; rfl
    intro i hi; rw [mul_smul_comm]

lemma symmSpan_pmul_dvd {p q r : MvPolynomial α F} (h : p = q * r) (hq : kSymmetric q) :
  symmSpan {p} = pmul q (symmSpan {r}) := by
    unfold symmSpan Ideal.span
    rw [pmul_span]
    apply Submodule.span_eq_span

    intro x
    simp only [mem_symmSet_singleton, Ideal.submodule_span_eq, SetLike.mem_coe, forall_exists_index]
    intro σ hx
    specialize hq σ; obtain ⟨c, hq⟩ := hq
    rw [← hx, h, smul_mul', hq, smul_eq_C_mul, mul_assoc]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    simp only [Set.mem_image, mem_symmSet_singleton, mul_eq_mul_left_iff, exists_exists_eq_and]
    use σ; left; rfl


    intro x
    simp only [Set.mem_image, mem_symmSet_singleton, exists_exists_eq_and, Ideal.submodule_span_eq,
      SetLike.mem_coe, forall_exists_index]
    intro σ hx
    obtain ⟨c, hq⟩ := perm_eq_c_perm_of_kSymm hq 1 σ
    rw [one_smul] at hq
    rw [← hx, hq, smul_eq_C_mul, mul_assoc, ← smul_mul', ← h]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    simp only [mem_symmSet_singleton, exists_apply_eq_apply]

lemma pmul_eq_mul_span {p : MvPolynomial α F} {I : Ideal (MvPolynomial α F)} :
  pmul p I = Ideal.span {p} * I := by
    let hI := Ideal.span_eq I
    nth_rw 2 [← hI]
    rw [Ideal.span_mul_span', Set.singleton_mul, Ideal.span, ← pmul_span, ← Ideal.span, hI]

lemma pmul_mul {p : MvPolynomial α F} {I J : Ideal (MvPolynomial α F)} :
  pmul p (I*J) = (pmul p I)*J := by
    rw [pmul_eq_mul_span, pmul_eq_mul_span, mul_assoc]

lemma pmul_inf {p : MvPolynomial α F} {M N : Submodule R (MvPolynomial α F)} :
  pmul p (M ⊓ N) = (pmul p M) ⊓ (pmul p N) := by
    by_cases hp0 : p = 0
    simp only [hp0, pmul_zero, Submodule.zero_eq_bot, le_refl, inf_of_le_left]

    ext q
    simp only [← SetLike.mem_coe, pmul_eq, Submodule.inf_coe, Set.mem_image, Set.mem_inter_iff]
    constructor; intro h
    obtain ⟨x, h⟩ := h; constructor
    use x; constructor; exact h.1.1; exact h.2
    use x; constructor; exact h.1.2; exact h.2
    intro ⟨hM, hN⟩
    obtain ⟨m, hm, hM⟩ := hM; obtain ⟨n, hn, hN⟩ := hN
    suffices m = n by
      use n; constructor; constructor; rw [← this]; exact hm
      exact hn; exact hN
    rw [← hM, mul_right_inj' hp0] at hN
    symm; exact hN

lemma pmul_restrictScalars {p : MvPolynomial α F} {I : Ideal (MvPolynomial α F)} :
  pmul p (Submodule.restrictScalars F I) = Submodule.restrictScalars F (pmul p I) := by
    ext q
    simp only [← SetLike.mem_coe, pmul_eq, Submodule.coe_restrictScalars, Set.mem_image]

lemma pmul_perm_le_symmSpan_mul {p : MvPolynomial α F} {σ : Equiv.Perm α} {J : Ideal (MvPolynomial α F)} :
  pmul (σ • p) J ≤ symmSpan {p} * J := by
    rw [pmul_eq_mul_span]
    apply Ideal.mul_mono_left
    apply Ideal.span_mono
    simp only [Set.singleton_subset_iff, mem_symmSet_singleton, exists_apply_eq_apply]

lemma pmul_le_symmSpan_mul {p : MvPolynomial α F} {J : Ideal (MvPolynomial α F)} :
  pmul p J ≤ symmSpan {p} * J := by
    nth_rw 1 [← one_smul (Equiv.Perm α) p]
    exact pmul_perm_le_symmSpan_mul

lemma minDeg_pmul_perm_eq_minDeg_symmSpan [DecidableEq α] {p : MvPolynomial α F} (σ : Equiv.Perm α) {n : ℕ} {J : Ideal (MvPolynomial α F)}
  (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) :
  minDeg (pmul (σ • p) J) = minDeg (symmSpan {p} * J) := by
    by_cases hJB : J = ⊥
    simp only [hJB, pmul_bot, Submodule.zero_eq_bot, minDeg_bot, Submodule.mul_bot]

    by_cases hp0 : p = 0
    simp only [hp0, smul_zero, pmul_zero, Submodule.zero_eq_bot, minDeg_bot, symmSpan_zero,
      Submodule.bot_mul]

    rw [pmul_eq_mul_span, minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB,
      minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB, minDeg_symmSpan hp hp0,
      Nat.add_right_cancel_iff]
    apply minDeg_homo
    simp only [Set.mem_singleton_iff, ne_eq, exists_eq_left]
    exact (smul_ne_zero_iff_ne σ).mpr hp0
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule]
    exact homo_symmAct σ hp

    exact singleDegGen_of_symmSpan hp
    rw [ne_eq, symmSpan_bot_iff]; exact hp0

    refine singleDegGen_iff.mpr ?_
    use n; use {σ • p}; constructor; swap; rfl
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule]
    exact homo_symmAct σ hp

    rw [ne_eq, Ideal.span_eq_bot]; push_neg
    simp only [Set.mem_singleton_iff, ne_eq, exists_eq_left]
    exact (smul_ne_zero_iff_ne σ).mpr hp0


lemma minDeg_pmul_eq_minDeg_symmSpan [DecidableEq α] {p : MvPolynomial α F} {n : ℕ} {J : Ideal (MvPolynomial α F)}
  (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) :
  minDeg (pmul p J) = minDeg (symmSpan {p} * J) := by
    let h := minDeg_pmul_perm_eq_minDeg_symmSpan 1 hJ hp
    rw [one_smul] at h
    exact h

lemma minDeg_pmul [DecidableEq α] {p : MvPolynomial α F} {n : ℕ} {J : Ideal (MvPolynomial α F)}
  (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) (hJB : J ≠ ⊥) (hp0 : p ≠ 0) :
  minDeg (pmul p J) = n + minDeg J := by
    have hp : ({p} : Set (MvPolynomial α F)) ⊆ (homogeneousSubmodule α F n) := by
      simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule]
      exact hp
    rw [pmul_eq_mul_span, minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB, minDeg_homo ?_ hp]
    simp only [Set.mem_singleton_iff, ne_eq, exists_eq_left]
    exact hp0
    rw [singleDegGen_iff]; use n; use {p}
    rw [ne_eq, Ideal.span_eq_bot]; push_neg
    simp only [Set.mem_singleton_iff, ne_eq, exists_eq_left]
    exact hp0


noncomputable def highestDegree (p : MvPolynomial α F) := sSup {i | homogeneousComponent i p ≠ 0}
noncomputable def lowestDegree (p : MvPolynomial α F) := sInf {i | homogeneousComponent i p ≠ 0}

@[simp] lemma highestDegree_zero : highestDegree (0 : MvPolynomial α F) = 0 := by
  unfold highestDegree
  suffices {i | homogeneousComponent i 0 ≠ 0} = ∅ by
    rw [this, csSup_empty, Nat.bot_eq_zero]
  simp only [map_zero, ne_eq, not_true_eq_false, Set.setOf_false]
@[simp] lemma lowestDegree_zero : lowestDegree (0 : MvPolynomial α F) = 0 := by
  unfold lowestDegree
  suffices {i | homogeneousComponent i 0 ≠ 0} = ∅ by
    rw [this, Nat.sInf_empty]
  simp only [map_zero, ne_eq, not_true_eq_false, Set.setOf_false]

lemma nonzero_homogeneousComponents_bddAbove {p : MvPolynomial α F} : BddAbove {i | homogeneousComponent i p ≠ 0} := by
  rw [bddAbove_def]; use p.totalDegree; intro i hi
  rw [Set.mem_setOf] at hi
  contrapose! hi
  exact homogeneousComponent_eq_zero i p hi

lemma nonzero_homogeneousComponents_nonempty {p : MvPolynomial α F} (hp : p ≠ 0) : {i | homogeneousComponent i p ≠ 0}.Nonempty := by
  rw [← sum_homogeneousComponent p] at hp
  apply Finset.exists_ne_zero_of_sum_ne_zero at hp
  obtain ⟨i, hi, hp⟩ := hp
  use i; rw [Set.mem_setOf]; exact hp

lemma lowestDegree_le_highestDegree (p : MvPolynomial α F) : lowestDegree p ≤ highestDegree p := by
  by_cases hp : p = 0
  simp only [hp, lowestDegree_zero, highestDegree_zero, le_refl]

  apply csInf_le_csSup ?_ nonzero_homogeneousComponents_bddAbove (nonzero_homogeneousComponents_nonempty hp)
  rw [bddBelow_def]; use 0
  simp only [ne_eq, Set.mem_setOf_eq, zero_le, implies_true]

lemma homogeneousComponent_eq_zero_of_lt_lowestDegree {p : MvPolynomial α F} {i : ℕ}
  (h : i < lowestDegree p) : homogeneousComponent i p = 0 := by
    contrapose! h
    apply Nat.sInf_le
    rw [Set.mem_setOf]; exact h

lemma highestDegree_component_ne_zero {p : MvPolynomial α F} (hp : p ≠ 0) : homogeneousComponent (highestDegree p) p ≠ 0 := by
  suffices highestDegree p ∈ {i | homogeneousComponent i p ≠ 0} by rw [Set.mem_setOf] at this; exact this
  exact Nat.sSup_mem (nonzero_homogeneousComponents_nonempty hp) nonzero_homogeneousComponents_bddAbove

lemma lowestDegree_component_ne_zero {p : MvPolynomial α F} (hp : p ≠ 0) : homogeneousComponent (lowestDegree p) p ≠ 0 := by
  suffices lowestDegree p ∈ {i | homogeneousComponent i p ≠ 0} by rw [Set.mem_setOf] at this; exact this
  exact Nat.sInf_mem (nonzero_homogeneousComponents_nonempty hp)

lemma highestDegree_eq_totalDegree {p : MvPolynomial α F} : highestDegree p = p.totalDegree := by
  by_cases hp0 : p = 0
  simp only [hp0, highestDegree_zero, totalDegree_zero]

  have hle : highestDegree p ≤ p.totalDegree := by
    by_contra! h
    apply homogeneousComponent_eq_zero at h
    exact highestDegree_component_ne_zero hp0 h
  apply antisymm hle
  unfold totalDegree highestDegree
  simp only [Finset.sup_le_iff, mem_support_iff, ne_eq]
  intro d hd
  unfold Finsupp.sum; simp only
  apply le_csSup nonzero_homogeneousComponents_bddAbove
  rw [Set.mem_setOf]
  contrapose! hd; apply_fun (coeff d) at hd
  rw [coeff_homogeneousComponent] at hd
  simp only [Finsupp.degree, ↓reduceIte, coeff_zero] at hd
  exact hd

theorem highestDegree_mul {p q : MvPolynomial α F} (hp : p ≠ 0) (hq : q ≠ 0) : highestDegree (p*q) = highestDegree p + highestDegree q := by
  simp only [highestDegree_eq_totalDegree]
  exact totalDegree_mul_of_isDomain hp hq

variable [DecidableEq α]

lemma homogeneousComponent_mul {p q : MvPolynomial α F} {n : ℕ} :
  homogeneousComponent n (p*q) = ∑ x ∈ Finset.antidiagonal n, (homogeneousComponent x.1 p) * (homogeneousComponent x.2 q) := by
    ext d; rw [coeff_sum, coeff_homogeneousComponent]
    by_cases hd : d.degree = n


    simp only [hd, ↓reduceIte];
    simp only [coeff_mul, coeff_homogeneousComponent, mul_ite, ite_mul, zero_mul, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr; rfl
    intro x hx; rw [Finset.mem_antidiagonal] at hx
    rw [Finset.sum_eq_single_of_mem (x.1.degree, x.2.degree)]
    simp only [↓reduceIte]
    rw [Finset.mem_antidiagonal]
    simp only; rw [← hd, ← hx, Finsupp.degree_add]

    intro y hy hyx
    simp only [ite_eq_right_iff, mul_eq_zero]
    intro hxy2 hxy1
    rw [hxy1, hxy2] at hyx
    simp only [Prod.mk.eta, ne_eq, not_true_eq_false] at hyx


    simp only [hd, ↓reduceIte]; symm
    apply Finset.sum_eq_zero; intro x hx
    rw [coeff_mul]; apply Finset.sum_eq_zero
    intro y hy
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    simp only [mul_ite, ite_mul, zero_mul, mul_zero, ite_eq_right_iff, mul_eq_zero]
    intro hxy2 hxy1
    rw [Finset.mem_antidiagonal] at hy; rw [Finset.mem_antidiagonal] at hx
    apply_fun Finsupp.degree at hy; rw [Finsupp.degree_add] at hy
    rw [← hy, ← hx, hxy1, hxy2] at hd
    simp only [not_true_eq_false] at hd


lemma homogeneousComponent_lowestDegree_add_mul {p q : MvPolynomial α F} :
  homogeneousComponent (lowestDegree p + lowestDegree q) (p*q) =
  (homogeneousComponent (lowestDegree p) p) * (homogeneousComponent (lowestDegree q) q) := by
    rw [homogeneousComponent_mul, Finset.sum_eq_single_of_mem (lowestDegree p, lowestDegree q)]
    rw [Finset.mem_antidiagonal]
    intro x hx hxl; rw [Finset.mem_antidiagonal] at hx
    wlog hxp : x.1 > lowestDegree p

    rw [add_comm x.1, add_comm (lowestDegree p)] at hx
    specialize this (x.2, x.1) hx ?_ ?_
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro hxq; contrapose! hxl
    rw [← hxq, ← hxl]
    simp only; push_neg at hxp
    contrapose! hxl;
    suffices x.1 = lowestDegree p ∧ x.2 = lowestDegree q by rw [← this.1, ← this.2]
    omega
    rw [mul_comm]; exact this

    have hxq : x.2 < lowestDegree q := by omega
    apply homogeneousComponent_eq_zero_of_lt_lowestDegree at hxq
    rw [hxq, mul_zero]

theorem lowestDegree_mul {p q : MvPolynomial α F} (hp : p ≠ 0) (hq : q ≠ 0) : lowestDegree (p*q) = lowestDegree p + lowestDegree q := by
  have hle : lowestDegree (p*q) ≤ lowestDegree p + lowestDegree q := by
    apply Nat.sInf_le; rw [Set.mem_setOf]
    rw [homogeneousComponent_lowestDegree_add_mul]
    exact mul_ne_zero (lowestDegree_component_ne_zero hp) (lowestDegree_component_ne_zero hq)
  apply antisymm hle
  apply le_csInf (nonzero_homogeneousComponents_nonempty (mul_ne_zero hp hq))

  intro i hi; rw [Set.mem_setOf] at hi
  suffices ∃ j k, j + k = i ∧ lowestDegree p ≤ j ∧ lowestDegree q ≤ k by
    obtain ⟨j, k, this⟩ := this
    omega
  rw [homogeneousComponent_mul] at hi
  apply Finset.exists_ne_zero_of_sum_ne_zero at hi
  obtain ⟨x, hi, hx⟩ := hi
  rw [Finset.mem_antidiagonal] at hi
  rw [mul_ne_zero_iff] at hx
  use x.1; use x.2; constructor; exact hi; constructor
  apply Nat.sInf_le; rw [Set.mem_setOf]; exact hx.1
  apply Nat.sInf_le; rw [Set.mem_setOf]; exact hx.2


theorem homogeneous_iff_lowestDegree_eq_highestDegree {p : MvPolynomial α F} :
  p.IsHomogeneous p.totalDegree ↔ highestDegree p = lowestDegree p := by
    by_cases hp0 : p = 0
    simp only [hp0, totalDegree_zero, isHomogeneous_zero, highestDegree_zero, lowestDegree_zero]

    constructor; intro h
    unfold highestDegree lowestDegree
    suffices {i | homogeneousComponent i p ≠ 0} = {p.totalDegree} by
      rw [this]; simp only [csSup_singleton, csInf_singleton]
    ext i; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [homogeneousComponent_of_mem h]
    simp only [ne_eq, ite_eq_right_iff, hp0, imp_false, Decidable.not_not]

    intro h
    suffices {i | homogeneousComponent i p ≠ 0} = {p.totalDegree} by
      suffices p = homogeneousComponent p.totalDegree p by
        nth_rw 1 [this]; exact homogeneousComponent_isHomogeneous p.totalDegree p
      suffices ∀ i < p.totalDegree, homogeneousComponent i p = 0 by
        nth_rw 1 [← sum_homogeneousComponent p]
        rw [Finset.sum_eq_single_of_mem]
        exact Finset.self_mem_range_succ p.totalDegree
        intro i hi hip
        apply this i
        rw [Finset.mem_range] at hi
        omega
      intro i; contrapose!; intro hi
      apply le_of_eq
      suffices i ∈ {p.totalDegree} by
        rw [Set.mem_singleton_iff] at this
        symm; exact this
      rw [← this, Set.mem_setOf]; exact hi
    ext i; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [← highestDegree_eq_totalDegree]

    constructor; intro hi
    have hle : i ≤ highestDegree p := by
      unfold highestDegree
      apply le_csSup nonzero_homogeneousComponents_bddAbove
      rw [Set.mem_setOf]; exact hi
    apply antisymm hle
    rw [h, lowestDegree]
    apply Nat.sInf_le
    rw [Set.mem_setOf]; exact hi

    intro hi; rw [hi]; exact highestDegree_component_ne_zero hp0

lemma homogeneous_of_dvd_homogeneous {p q : MvPolynomial α F} {n : ℕ} (hp : p.IsHomogeneous n)
  (hp0 : p ≠ 0) (h : q ∣ p) : q.IsHomogeneous q.totalDegree := by
    obtain ⟨r, hr⟩ := h
    let hp0' := hp0; rw [hr, mul_ne_zero_iff] at hp0'
    obtain ⟨hq0, hr0⟩ := hp0'
    rw [homogeneous_iff_lowestDegree_eq_highestDegree]
    have hhd : highestDegree p = highestDegree q + highestDegree r := by
      apply_fun highestDegree at hr; rw [highestDegree_mul hq0 hr0] at hr; exact hr
    have hld : lowestDegree p = lowestDegree q + lowestDegree r := by
      apply_fun lowestDegree at hr; rw [lowestDegree_mul hq0 hr0] at hr; exact hr
    have hn : n = p.totalDegree := by symm; exact IsHomogeneous.totalDegree hp hp0
    rw [hn, homogeneous_iff_lowestDegree_eq_highestDegree] at hp
    rw [hhd, hld] at hp
    let hq := lowestDegree_le_highestDegree q
    let hr := lowestDegree_le_highestDegree r
    omega

lemma homoSubI_pmul {p : MvPolynomial α F} {I : Ideal (MvPolynomial α F)} {n : ℕ}
  (hp : p.IsHomogeneous n) (hI : IsSingleDegGen I) :
  homogeneousSubmoduleI (minDeg (pmul p I)) (pmul p I) =
  pmul p (homogeneousSubmoduleI (minDeg I) I) := by
    by_cases hIB : I = ⊥
    simp only [hIB, pmul_bot, Submodule.zero_eq_bot, minDeg_bot]
    simp only [← Submodule.zero_eq_bot, homoSubI_zero]
    simp only [Submodule.zero_eq_bot, pmul_bot]

    by_cases hp0 : p = 0
    simp only [hp0, pmul_zero, Submodule.zero_eq_bot, minDeg_bot]
    simp only [← Submodule.zero_eq_bot, homoSubI_zero]

    unfold homogeneousSubmoduleI
    rw [pmul_inf, pmul_restrictScalars, inf_eq_inf_iff_right]
    constructor

    intro q
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule, and_imp]
    intro hq hqI
    simp only [← SetLike.mem_coe, pmul_eq, Set.mem_image] at hq
    obtain ⟨r, hr, hq⟩ := hq
    simp only [SetLike.mem_coe, mem_homogeneousSubmodule] at hr
    rw [minDeg_pmul hI hp hIB hp0, ← hq]
    exact IsHomogeneous.mul hp hr

    intro q
    by_cases hq0 : q = 0
    simp only [hq0, Submodule.zero_mem, imp_self]

    simp only [Submodule.mem_inf, mem_homogeneousSubmodule, Submodule.restrictScalars_mem, and_imp]
    intro hq hqI
    simp only [← SetLike.mem_coe, pmul_eq, Set.mem_image]
    simp only [← SetLike.mem_coe, pmul_eq, Set.mem_image] at hqI
    obtain ⟨r, hrI, hr⟩ := hqI
    have hp0 : p ≠ 0 := by contrapose! hq0; rw [← hr, hq0, zero_mul]
    use r; constructor; swap; exact hr
    simp only [SetLike.mem_coe, mem_homogeneousSubmodule]
    rw [minDeg_pmul hI hp hIB hp0] at hq
    have hrq : r ∣ q := by use p; symm; rw [mul_comm]; exact hr
    let hrh := homogeneous_of_dvd_homogeneous hq hq0 hrq
    suffices r.totalDegree = minDeg I by rw [← this]; exact hrh
    apply IsHomogeneous.mul hp at hrh
    rw [hr] at hrh
    apply IsHomogeneous.inj_right hrh hq at hq0
    exact Nat.add_left_cancel hq0


lemma pmul_singleDegGen_iff {p : MvPolynomial α F} {I : Ideal (MvPolynomial α F)} {n : ℕ} (hp0 : p ≠ 0)
  (hp : p.IsHomogeneous n) :
  IsSingleDegGen (pmul p I) ↔ IsSingleDegGen I := by
    constructor; intro h;
    rw [singleDegGen_iff] at h; rw [singleDegGen_iff]
    obtain ⟨m, S, hS, h⟩ := h
    use m-n
    have hSp : ∀ g ∈ S, ∃ q, g = p * q := by
      intro g hg; apply Ideal.subset_span at hg
      rw [← h, pmul_eq, Set.mem_image] at hg
      obtain ⟨q, _, hg⟩ := hg
      use q; symm; exact hg
    use Set.range (fun g : S => Classical.choose (hSp g.1 g.2))
    constructor
    intro q
    simp only [Set.mem_range, Subtype.exists, SetLike.mem_coe, mem_homogeneousSubmodule,
      forall_exists_index]
    intro g hg hgq
    have hgq : g = p * q := by rw [← hgq]; exact Classical.choose_spec (hSp g hg)
    by_cases hq0 : q = 0
    rw [hq0]; exact isHomogeneous_zero α F (m - n)
    apply mul_ne_zero hp0 at hq0; rw [← hgq] at hq0
    have hq : q.IsHomogeneous q.totalDegree := by
      apply hS at hg; simp only [SetLike.mem_coe, mem_homogeneousSubmodule] at hg
      apply homogeneous_of_dvd_homogeneous hg hq0
      use p; rw [mul_comm]; exact hgq
    suffices q.totalDegree = m - n by rw [← this]; exact hq
    apply hS at hg; simp only [SetLike.mem_coe, mem_homogeneousSubmodule] at hg
    apply IsHomogeneous.mul hp at hq; rw [← hgq] at hq
    apply IsHomogeneous.inj_right hg hq at hq0
    exact Nat.eq_sub_of_add_eq' (id (Eq.symm hq0))

    apply Ideal.span_singleton_mul_right_injective hp0
    simp only
    rw [← pmul_eq_mul_span, Ideal.span_mul_span', h]; congr
    ext g; simp only [Set.singleton_mul, Set.mem_image, Set.mem_range, Subtype.exists]
    constructor; intro hg
    specialize hSp g hg;
    use Classical.choose hSp; constructor; use g; use hg;
    symm; exact Classical.choose_spec hSp
    intro h'
    obtain ⟨q, ⟨g', ⟨hg', hq⟩⟩, h'⟩ := h'
    have hgq : g' = p*q := by
      rw [← hq]
      exact Classical.choose_spec (hSp g' hg')
    rw [← h', ← hgq]; exact hg'


    unfold IsSingleDegGen
    intro h; nth_rw 1 [h]
    rw [homoSubI_pmul hp h]; nth_rw 2 [Ideal.span]
    rw [pmul_eq, ← pmul_span, ← Ideal.span]

variable [Finite α]

lemma pmul_mgs_eq (p : MvPolynomial α F) {I : Ideal (MvPolynomial α F)} {n : ℕ}
  (hI : IsSingleDegGen I) (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) :
  min_gen_size (pmul p I) = min_gen_size I := by
    let hpI := (pmul_singleDegGen_iff hp0 hp).mpr hI
    rw [mgs_eq_rank hpI, mgs_eq_rank hI, homoSubI_pmul hp hI, ← rank_eq_pmul_rank p hp0]



lemma mgs_one_le_mgs_mul' {J : Ideal (MvPolynomial α F)} {p : MvPolynomial α F} {n : ℕ} (σ : Equiv.Perm α)
  (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) (hp0 : p ≠ 0)
  (h : Module.finrank F (pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)) -
    Module.finrank F ((pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)) ⊓ (pmul p (homogeneousSubmoduleI (minDeg J) J)) : Submodule F (MvPolynomial α F)) ≥ 1)
  : min_gen_size J + 1 ≤ min_gen_size ((symmSpan {p})*J) := by
    rw [mgs_eq_rank hJ, mgs_eq_rank (singleDegGen_mul (singleDegGen_of_symmSpan hp) hJ)]
    have hσ : (σ • p).IsHomogeneous n := by exact homo_symmAct σ hp
    let U := homogeneousSubmoduleI (minDeg ((symmSpan {p})*J)) ((symmSpan {p})*J)
    let V := pmul (σ • p) (homogeneousSubmoduleI (minDeg J) J)
    let W := pmul p (homogeneousSubmoduleI (minDeg J) J)
    have hU : Module.Finite F U := by apply homoSubI_mod_fin
    have hV : Module.Finite F V := by unfold V; rw [← homoSubI_pmul hσ hJ]; apply homoSubI_mod_fin
    have hW : Module.Finite F W := by unfold W; rw [← homoSubI_pmul hp hJ]; apply homoSubI_mod_fin
    calc Module.finrank F U
      _ ≥ Module.finrank F (V ⊔ W : Submodule F (MvPolynomial α F)) := by
        apply Submodule.finrank_mono
        unfold U V W
        apply sup_le
        rw [← homoSubI_pmul hσ hJ, minDeg_pmul_perm_eq_minDeg_symmSpan σ hJ hp]
        apply homoSubI_monotone (minDeg (symmSpan {p} * J)) (pmul_perm_le_symmSpan_mul)

        rw [← homoSubI_pmul hp hJ, minDeg_pmul_eq_minDeg_symmSpan hJ hp]
        apply homoSubI_monotone (minDeg (symmSpan {p} * J)) (pmul_le_symmSpan_mul)
      _ ≥ Module.finrank F V + Module.finrank F W - Module.finrank F (V ⊓ W : Submodule F (MvPolynomial α F)) := by
          simp only [ge_iff_le, tsub_le_iff_right]
          apply le_of_eq; symm
          exact Submodule.finrank_sup_add_finrank_inf_eq V W
      _ = Module.finrank F W + (Module.finrank F V - Module.finrank F (V ⊓ W : Submodule F (MvPolynomial α F))) := by
        rw [← Nat.add_sub_assoc, Nat.add_comm]
        apply Submodule.finrank_mono inf_le_left
      _ ≥ Module.finrank F W + 1 := by
        rw [ge_iff_le, add_le_add_iff_left (Module.finrank F W)]
        exact h
      _ = Module.finrank F (homogeneousSubmoduleI (minDeg J) J) + 1 := by
        congr 1; unfold W; symm
        apply rank_eq_pmul_rank p hp0



theorem max_mgs_le_mgs_prod {p : MvPolynomial α F} {n : ℕ} {J : Ideal (MvPolynomial α F)}
  (hp : p.IsHomogeneous n) (hpk : ¬ kSymmetric p) (hJ : IsSingleDegGen J) (hJB : J ≠ ⊥) :
  min_gen_size J  + 1 ≤ min_gen_size ((symmSpan {p}) * J) := by
    have hfin  : Fintype (symmSet {p}) := by apply Fintype.ofFinite ↑(⋃ σ, (fun x ↦ σ • x) '' {p})
    let q := ((symmSet {p}).toFinset).val.gcd
    have hpq : q ∣ p := by
      apply Multiset.gcd_dvd
      simp only [Finset.mem_val, Set.mem_toFinset, mem_symmSet_singleton_self]

    obtain ⟨p', hpq⟩ := hpq
    have hpz : p ≠ 0 := by contrapose! hpk; rw [hpk]; exact kSymmetric_zero
    have hp'h : p'.IsHomogeneous p'.totalDegree := by
      apply homogeneous_of_dvd_homogeneous hp hpz
      use q; rw [mul_comm]; exact hpq
    have hqh : q.IsHomogeneous q.totalDegree := by
      apply homogeneous_of_dvd_homogeneous hp hpz; use p'
    have hq : kSymmetric q := by exact gcd_symmSet_kSymmetric
    let hp0 := hpz; rw [hpq, mul_ne_zero_iff] at hp0
    obtain ⟨hqz, hpz'⟩ := hp0
    have hp' : ∃ r, ∃ σ : Equiv.Perm α, Prime r ∧ r ∣ p' ∧ ¬r ∣ σ • p' := by
      have hr : ∃ r, Prime r ∧ r ∣ p' := by
        let hpf := UniqueFactorizationMonoid.exists_prime_factors p' hpz'
        obtain ⟨f, hpf, hfp'⟩ := hpf
        have hfne : ∃ r, r ∈ f := by
          contrapose! hpk
          apply Multiset.eq_zero_of_forall_notMem at hpk
          rw [hpk, Multiset.prod_zero, Associated.comm,
            associated_one_iff_isUnit, isUnit_iff_eq_C_of_isReduced] at hfp'
          obtain ⟨c, hcu, hc⟩ := hfp'
          rw [hpq, hc]
          intro σ; specialize hq σ
          obtain ⟨c', hq⟩ := hq; use c'
          rw [smul_mul', hq, symmAct_def, rename_C, smul_eq_C_mul, smul_eq_C_mul, mul_assoc]
        obtain ⟨r, hrf⟩ := hfne
        use r; constructor; exact hpf r hrf
        rw [← Associated.dvd_iff_dvd_right hfp']
        exact Multiset.dvd_prod hrf
      obtain ⟨r, hr⟩ := hr
      use r; by_contra! hσ
      simp only [hr, forall_const] at hσ
      suffices q*r ∣ q by
        obtain ⟨u, hu⟩ := this
        nth_rw 1 [← mul_one q] at hu
        rw [mul_assoc, mul_right_inj' hqz] at hu
        have hru : IsUnit r := by
          rw [isUnit_iff_exists_inv]; use u; symm; exact hu
        unfold Prime at hr
        exact hr.1.2.1 hru
      rw [Multiset.dvd_gcd]; intro b hb
      simp only [Finset.mem_val, Set.mem_toFinset, mem_symmSet_singleton] at hb
      obtain ⟨σ, hb⟩ := hb
      rw [← hb, hpq, smul_mul']
      obtain ⟨a, ha⟩ := hσ σ;
      specialize hq σ; obtain ⟨c, hq⟩ := hq
      use C c * a; rw [ha, hq, smul_eq_C_mul]; ring
    obtain ⟨r, σ, hr, hrp', hrσ⟩ := hp'

    have hprJ : min_gen_size (symmSpan {p} * J) = min_gen_size (symmSpan {p'} * J) := by
      rw [mgs_eq_rank (singleDegGen_mul (singleDegGen_of_symmSpan hp'h) hJ),
        mgs_eq_rank (singleDegGen_mul (singleDegGen_of_symmSpan hp) hJ)]
      nth_rw 2 [rank_eq_pmul_rank q hqz]
      rw [← homoSubI_pmul hqh (singleDegGen_mul (singleDegGen_of_symmSpan hp'h) hJ), pmul_mul, symmSpan_pmul_dvd hpq hq]
    rw [hprJ]

    obtain ⟨T, hT, hTJ⟩ := singleDegGen_iff_fin_homo_span.mp hJ
    have hdemp : DecidableEq (MvPolynomial α F) := by exact Classical.typeDecidableEq (MvPolynomial α F)
    let S := Finset.erase T 0
    have hS : S.toSet ⊆ (homogeneousSubmodule α F (minDeg J)) := by
      apply subset_trans ?_ hT
      apply Finset.erase_subset
    have hSJ : J = Ideal.span S := by
      unfold S; rw [hTJ]; apply Submodule.span_eq_span
      intro t ht; by_cases ht0 : t = 0
      rw [ht0]
      simp only [Finset.coe_erase, Ideal.submodule_span_eq, SetLike.mem_coe,
        Submodule.zero_mem]
      apply Submodule.subset_span
      simp only [Finset.coe_erase, Set.mem_diff, ht, Set.mem_singleton_iff, ht0, not_false_eq_true,
        and_self]

      apply subset_trans ?_ Submodule.subset_span
      apply Finset.erase_subset
    have hSe' : ∃ x ∈ S, x ≠ 0 := by
      contrapose! hJB
      rw [hSJ, Ideal.span_eq_bot]
      exact hJB
    have hSe : S.val.gcd ≠ 0 := by
      rw [ne_eq, Multiset.gcd_eq_zero_iff]; push_neg
      simp only [Finset.mem_val]; exact hSe'
    have hSh : (S.val.gcd).IsHomogeneous S.val.gcd.totalDegree := by
      obtain ⟨g, hg, hgz⟩ := hSe'
      apply homogeneous_of_dvd_homogeneous ?_ hgz (Multiset.gcd_dvd hg)
      use (minDeg J); apply hS at hg
      simp only [SetLike.mem_coe, mem_homogeneousSubmodule] at hg
      exact hg
    let S' := (Set.range (fun f : S => Classical.choose (Multiset.gcd_dvd f.2)))
    let J' := Ideal.span S'
    have hJ' : J = pmul (S.val.gcd) J' := by
      rw [hSJ]; unfold J'
      nth_rw 2 [Ideal.span]; rw [pmul_span]; congr; ext g; constructor

      intro hgS; rw [Set.mem_image]
      let hgcd := Multiset.gcd_dvd hgS
      use Classical.choose hgcd; constructor; unfold S'
      simp only [Set.mem_range, Subtype.exists]
      use g; use hgS; symm
      exact Classical.choose_spec hgcd

      intro hgS'; rw [Set.mem_image] at hgS'
      obtain ⟨g', hgS', hgg⟩ := hgS'
      unfold S' at hgS'
      rw [Set.mem_range, Subtype.exists] at hgS'
      obtain ⟨g₁, hg₁, hgg₁⟩ := hgS'
      have hSgg₁ : S.val.gcd * g' = g₁ := by
        rw [← hgg₁]; symm
        exact Classical.choose_spec (Multiset.gcd_dvd hg₁)
      rw [← hgg, hSgg₁]; exact hg₁
    have hJ's : IsSingleDegGen J' := by
      rw [← pmul_singleDegGen_iff hSe hSh, ← hJ']
      exact hJ
    have hJJ' : min_gen_size J = min_gen_size J' := by
      rw [hJ']; exact pmul_mgs_eq (S.val.gcd) hJ's hSh hSe
    have hJJ'r : min_gen_size (symmSpan {p'} * J) = min_gen_size (symmSpan {p'} * J') := by
      rw [hJ', mul_comm, ← pmul_mul, mul_comm]
      exact pmul_mgs_eq (S.val.gcd) (singleDegGen_mul (singleDegGen_of_symmSpan hp'h) hJ's) hSh hSe
    rw [hJJ', hJJ'r]
    obtain ⟨T'', hT'', hJT''⟩ := singleDegGen_iff_fin_homo_span.mp hJ's
    let S'' := Finset.erase T'' 0
    have hS'' : S''.toSet ⊆ (homogeneousSubmodule α F (minDeg J')) := by
      apply subset_trans ?_ hT''
      apply Finset.erase_subset
    have hJS'' : J' = Ideal.span S'' := by
      unfold S''; rw [hJT'']; apply Submodule.span_eq_span
      intro t ht; by_cases ht0 : t = 0
      rw [ht0]
      simp only [Finset.coe_erase, Ideal.submodule_span_eq, SetLike.mem_coe,
        Submodule.zero_mem]
      apply Submodule.subset_span
      simp only [Finset.coe_erase, Set.mem_diff, ht, Set.mem_singleton_iff, ht0, not_false_eq_true,
        and_self]

      apply subset_trans ?_ Submodule.subset_span
      apply Finset.erase_subset
    have hJ'g : ∃ g ∈ S'', ¬ r ∣ g  := by
      have hSu : IsUnit (S'.toFinset.val.gcd) := by
        suffices S.val.gcd*S'.toFinset.val.gcd ∣ S.val.gcd by
          obtain ⟨u, hu⟩ := this
          nth_rw 1 [← mul_one S.val.gcd, mul_assoc] at hu
          rw [mul_right_inj'] at hu
          rw [isUnit_iff_exists_inv]
          use u; symm; exact hu
          exact hSe
        rw [Multiset.dvd_gcd]
        intro f hf; rw [Finset.mem_val] at hf
        let hfg := Multiset.gcd_dvd hf
        have hgS' : (Classical.choose hfg) ∈ S'.toFinset := by
          unfold S'; simp only [Set.toFinset_range, Finset.univ_eq_attach, Finset.mem_image,
            Finset.mem_attach, true_and, Subtype.exists]
          use f; use hf
        obtain ⟨g', hfg'⟩ := Multiset.gcd_dvd hgS'
        let hfgg := Classical.choose_spec hfg
        rw [hfgg, hfg']
        use g'; rw [mul_assoc]
      contrapose! hr; unfold Prime;
      rw [not_and_or, not_and_or]; push_neg; right; left
      apply isUnit_of_dvd_unit ?_ hSu
      rw [Multiset.dvd_gcd]
      simp only [Finset.mem_val, Set.mem_toFinset]
      intro g hg
      have hgJ : g ∈ Ideal.span S'' := by
        rw [← hJS'']; unfold J';
        apply Ideal.subset_span hg
      rw [Ideal.span, Submodule.mem_span_finset] at hgJ
      obtain ⟨f, hf, hgs⟩ := hgJ; rw [← hgs]
      apply Finset.dvd_sum; intro g'' hg''
      rw [smul_eq_mul]
      apply Dvd.dvd.mul_left (hr g'' hg'') (f g'')


    apply mgs_one_le_mgs_mul' σ hJ's hp'h hpz'

    contrapose! hJ'g
    rw [Nat.lt_one_iff] at hJ'g
    apply Nat.le_of_sub_eq_zero at hJ'g
    have hminf : Module.Finite F (pmul (σ • p') (homogeneousSubmoduleI (minDeg J') J')) := by
      apply homo_symmAct σ at hp'h
      rw [← homoSubI_pmul hp'h hJ's]; apply homoSubI_mod_fin
    apply Submodule.eq_of_le_of_finrank_le inf_le_left at hJ'g
    intro g hgS
    have hg : (σ • p')*g ∈ pmul (σ • p') (homogeneousSubmoduleI (minDeg J') J') := by
      apply mem_pmul_of_mul_mem
      rw [homogeneousSubmoduleI, Submodule.mem_inf, Submodule.restrictScalars_mem]
      constructor
      apply hS''; exact hgS
      rw [hJS'']; apply Ideal.subset_span
      exact hgS
    have hrg : p' ∣ (σ • p')*g := by
      rw [← hJ'g, Submodule.mem_inf] at hg
      apply And.right at hg
      apply dvd_of_mem_pmul _ hg
    apply dvd_trans hrp' at hrg
    unfold Prime at hr
    apply And.right at hr; apply And.right at hr
    specialize hr (σ • p') g hrg
    simp only [hrσ, false_or] at hr
    exact hr



theorem max_mgs_le_mgs_prod_psi {p q : MvPolynomial α F} {n m : ℕ} (hp : p.IsHomogeneous n)
  (hq : q.IsHomogeneous m) (hpk : ¬ kSymmetric p) (hqk : ¬ kSymmetric q) :
  max (min_gen_size (symmSpan {p})) (min_gen_size (symmSpan {q})) + 1 ≤ min_gen_size ((symmSpan {p}) * (symmSpan {q})) := by
    apply Nat.add_le_of_le_sub
    apply mgs_pos
    rw [← Ideal.zero_eq_bot]
    apply mul_ne_zero

    contrapose! hpk
    rw [symmSpan, Ideal.zero_eq_bot, Ideal.span_eq_bot] at hpk
    specialize hpk p (mem_symmSet_singleton_self)
    rw [hpk]; exact kSymmetric_zero

    contrapose! hqk
    rw [symmSpan, Ideal.zero_eq_bot, Ideal.span_eq_bot] at hqk
    specialize hqk q (mem_symmSet_singleton_self)
    rw [hqk]; exact kSymmetric_zero


    apply max_le

    apply Nat.le_sub_of_add_le
    rw [mul_comm]
    apply max_mgs_le_mgs_prod hq hqk (singleDegGen_of_symmSpan hp) (symmSpan_not_bot_of_not_kSymmetric hpk)


    apply Nat.le_sub_of_add_le
    apply max_mgs_le_mgs_prod hp hpk (singleDegGen_of_symmSpan hq) (symmSpan_not_bot_of_not_kSymmetric hqk)
