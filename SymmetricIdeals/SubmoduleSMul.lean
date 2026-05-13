import Mathlib
import SymmetricIdeals.MinDeg
import SymmetricIdeals.SingleDegGen
import SymmetricIdeals.Basic
import SymmetricIdeals.Products.kSymmetric

variable {R S : Type*} [Semiring R] [Semiring S] [Module R S] [SMulCommClass R S S]

noncomputable
def pmul (p : S) (M : Submodule R S) := Submodule.span R ((p * ·) '' M)

variable {p q : S} {M : Submodule R S}

omit [SMulCommClass R S S] in
lemma mem_pmul_of_mul_mem (p q) (hq : q ∈ M) : p * q ∈ pmul p M := by
  apply Submodule.subset_span
  simp only [Set.mem_image, SetLike.mem_coe]
  use q


lemma pmul_eq : pmul p M = (p * ·) '' M := by
    ext x
    simp only [pmul, SetLike.mem_coe, Set.mem_image]
    constructor
    · intro h
      rw [Submodule.mem_span_image_iff_exists_fun] at h
      obtain ⟨T, hT, ⟨c, hc⟩⟩ := h
      use (∑ i, c i • i)
      constructor
      · refine Submodule.sum_mem _ ?_
        intro i hi
        exact Submodule.smul_mem _ _ <| hT <| Subtype.coe_prop _
      · rw [← hc, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_smul_comm]
    · intro ⟨y, hy, h⟩
      rw [← h]
      exact mem_pmul_of_mul_mem p y hy

@[simp]
lemma pmul_zero : pmul 0 M = 0 := by
  rw [Submodule.zero_eq_bot, Submodule.eq_bot_iff]
  intro x
  rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
  intro ⟨y, hy, hyx⟩
  rw [← hyx, zero_mul]

@[simp]
lemma pmul_bot : pmul p (⊥ : Submodule R S) = 0 := by
  rw [Submodule.zero_eq_bot, Submodule.eq_bot_iff]
  intro x
  rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
  grind [Submodule.bot_coe]


lemma pmul_bij [IsDomain S] (p : S) (M : Submodule R S) (hp : p ≠ 0) :
    Function.Bijective ((fun q => ⟨p * q, mem_pmul_of_mul_mem _ _ q.2⟩) : M → (pmul p M)) := by
  constructor
  · intro m n hnm
    simpa [hp] using hnm
  · intro q
    simp only [Subtype.exists]
    have hq : q.1 ∈ (p * ·) '' M := by simp [← pmul_eq]
    rw [Set.mem_image] at hq
    obtain ⟨a, ha, hq⟩ := hq
    use a, ha
    simp [hq]

noncomputable
def pmul_linear_map (p : S) (M : Submodule R S) :
  M →ₗ[R] (pmul p M) := ⟨⟨fun q => ⟨p * q, mem_pmul_of_mul_mem _ _ q.2⟩, by simp [mul_add]⟩,
    by simp [mul_smul_comm]⟩

noncomputable
def pmul_equiv [IsDomain S] (p : S) (M : Submodule R S) (hp : p ≠ 0) :
  M ≃ₗ[R] (pmul p M) := LinearEquiv.ofBijective (pmul_linear_map p M) (pmul_bij p M hp)

lemma rank_eq_pmul_rank [IsDomain S] (p : S) {M : Submodule R S} (hp : p ≠ 0) :
  Module.finrank R M = Module.finrank R (pmul p M) := LinearEquiv.finrank_eq (pmul_equiv p M hp)


lemma dvd_of_mem_pmul {p q : S} (M : Submodule R S)
    (h : q ∈ pmul p M) : p ∣ q := by
  unfold pmul at h
  rw [Submodule.mem_span_iff_exists_finset_subset] at h
  obtain ⟨f, T, hT, hf, hq⟩ := h
  rw [← hq]
  refine Finset.dvd_sum ?_
  intro t ht
  apply hT at ht
  simp only [Set.mem_image, SetLike.mem_coe] at ht
  obtain ⟨x, hx, ht⟩ := ht
  have hpt : p ∣ t := by
    use x
    exact ht.symm
  exact dvd_smul_of_dvd _ hpt

-- TODO: can this be done better
--  at the very least, one direction should be trivial since pmul p is a linear map
lemma pmul_span {p : S} {s : Set S} :
    pmul p (Submodule.span R s) = Submodule.span R ((p * ·) '' s) := by
  ext q
  constructor
  · intro hq
    have hq : q ∈ (p * ·) '' (Submodule.span R s) := by simpa [← pmul_eq]
    rw [Set.mem_image] at hq
    obtain ⟨r, hr, hq⟩ := hq
    rw [SetLike.mem_coe, Submodule.mem_span_iff_exists_finset_subset] at hr
    obtain ⟨f, T, hT, hf, hr⟩ := hr
    rw [← hq, ← hr, Finset.mul_sum]
    refine Submodule.sum_mem _ ?_
    intro t ht
    apply hT at ht
    rw [mul_smul_comm]
    refine Submodule.smul_mem _ _ <| Submodule.mem_span_of_mem ?_
    rw [Set.mem_image]
    use t
  intro hq
  rw [Submodule.mem_span_image_iff_exists_fun] at hq
  obtain ⟨T, hT, f, hq⟩ := hq
  rw [← SetLike.mem_coe, pmul_eq, Set.mem_image]
  use ∑ i, f i • i
  constructor
  · rw [SetLike.mem_coe]
    refine Submodule.sum_mem _ ?_
    intro i hi
    exact Submodule.smul_mem _ _ <| Submodule.mem_span_of_mem <| hT i.2
  · simp [← hq, Finset.mul_sum, mul_smul_comm]

lemma pmul_inf [IsDomain S] {p : S} {M N : Submodule R S} :
    pmul p (M ⊓ N) = (pmul p M) ⊓ (pmul p N) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  ext q
  simp [← SetLike.mem_coe, pmul_eq, Submodule.coe_inf, Set.mem_image, Set.mem_inter_iff]
  grind [mul_right_inj' hp0]

variable {R S : Type*} [Semiring R] [CommSemiring S] [Module R S]

lemma pmul_eq_span_mul {p : S} {I : Ideal S} :
    pmul p I = Ideal.span {p} * I := by
  conv => rhs; rw [← Ideal.span_eq I, Ideal.span_mul_span, Set.singleton_mul, Ideal.span,
    ← pmul_span, ← Ideal.span, Ideal.span_eq]

lemma pmul_mul {p : S} {I J : Ideal S} : pmul p (I * J) = (pmul p I) * J := by
  rw [pmul_eq_span_mul, pmul_eq_span_mul, mul_assoc]

lemma pmul_mul' {p : S} {I J : Ideal S} : pmul p (I * J) = I * (pmul p J) := by
  rw [mul_comm, pmul_mul, mul_comm]



section MvPolynomial

open MvPolynomial Rename

variable {α R : Type*} [CommSemiring R]

lemma symmSpan_eq_pmul_symmSpan {p q r : MvPolynomial α R} (h : p = q * r) (hq : kSymmetric q) :
    symmSpan {p} = pmul q (symmSpan {r}) := by
  rw [pmul_eq_span_mul, ← symmSpan_eq_span_of_kSymmetric hq, mul_symmSpan_of_kSymmetric hq, h]


lemma pmul_restrictScalars {p : MvPolynomial α R} {I : Ideal (MvPolynomial α R)} :
    pmul p (Submodule.restrictScalars R I) = Submodule.restrictScalars R (pmul p I) := by
  ext q
  simp only [← SetLike.mem_coe, pmul_eq, Submodule.coe_restrictScalars, Set.mem_image]

lemma pmul_perm_le_symmSpan_mul {p : MvPolynomial α R} {σ : Equiv.Perm α}
    {J : Ideal (MvPolynomial α R)} : pmul (σ • p) J ≤ symmSpan {p} * J := by
  rw [pmul_eq_span_mul]
  exact Ideal.mul_mono_left <| Ideal.span_mono (by simp)

lemma pmul_le_symmSpan_mul {p : MvPolynomial α R} {J : Ideal (MvPolynomial α R)} :
    pmul p J ≤ symmSpan {p} * J := by
  nth_rw 1 [← one_smul (Equiv.Perm α) p]
  exact pmul_perm_le_symmSpan_mul

variable [NoZeroDivisors R]

-- It suffices to have J.IsHomogeneous by using the fact that minDeg_mul works with just
--   homogeneous ideals.  Currently, that lemma is in the MinGens project.
lemma minDeg_pmul_perm_eq_minDeg_symmSpan {p : MvPolynomial α R} (σ : Equiv.Perm α) {n : ℕ}
    {J : Ideal (MvPolynomial α R)} (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) :
    minDeg (pmul (σ • p) J) = minDeg (symmSpan {p} * J) := by
  by_cases! hJB : J = ⊥
  · simp [hJB]
  by_cases! hp0 : p = 0
  · simp [hp0]
  have hσ : {σ • p} ⊆ SetLike.coe (homogeneousSubmodule α R n) := by
    simp [perm_isHomogeneous σ hp]
  rw [pmul_eq_span_mul, minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB,
    minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB, minDeg_symmSpan hp hp0, Nat.add_right_cancel_iff]
  · exact minDeg_homog (by simp [smul_ne_zero_iff_ne, hp0]) hσ
  · exact isSingleDegGen_symmSpan hp
  · rwa [ne_eq, symmSpan_bot_iff]
  · rw [isSingleDegGen_iff]
    use n, {σ • p}
  · simp [smul_ne_zero_iff_ne, hp0]

lemma minDeg_pmul_eq_minDeg_symmSpan {p : MvPolynomial α R} {n : ℕ} {J : Ideal (MvPolynomial α R)}
    (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) :
    minDeg (pmul p J) = minDeg (symmSpan {p} * J) := by
  have h := minDeg_pmul_perm_eq_minDeg_symmSpan 1 hJ hp
  rwa [one_smul] at h

lemma minDeg_pmul {p : MvPolynomial α R} {n : ℕ} {J : Ideal (MvPolynomial α R)}
    (hJ : IsSingleDegGen J) (hp : p.IsHomogeneous n) (hJB : J ≠ ⊥) (hp0 : p ≠ 0) :
    minDeg (pmul p J) = n + minDeg J := by
  have hp : ({p} : Set (MvPolynomial α R)) ⊆ (homogeneousSubmodule α R n) := by simp [hp]
  rw [pmul_eq_span_mul, minDeg_mul_eq_add_minDeg ?_ hJ ?_ hJB, minDeg_homog ?_ hp]
  · simp [hp0]
  · rw [isSingleDegGen_iff]
    use n, {p}
  · simp [hp0]

end MvPolynomial
