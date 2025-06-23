import Mathlib
import SymmetricIdeals.MinDeg
import SymmetricIdeals.Basic

open MvPolynomial

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable
def IsSingleDegGen (I : Ideal (MvPolynomial α F)) := I = Ideal.span (homogeneousSubmoduleI (minDeg I) I)


@[simp] lemma zero_singleDegGen : IsSingleDegGen (0 : Ideal (MvPolynomial α F)) := by
  unfold IsSingleDegGen
  rw [homoSubI_zero]
  exact Eq.symm (ideal_span_subset_zero_singleton fun ⦃a⦄ ↦ congrArg fun ⦃a⦄ ↦ a)

theorem singleDegGen_iff [DecidableEq α] : IsSingleDegGen I ↔ ∃ n : ℕ, ∃ S : Set (MvPolynomial α F), S ⊆ (homogeneousSubmodule α F n) ∧ I = Ideal.span S := by
  constructor; intro h
  use (minDeg I); use (homogeneousSubmoduleI (minDeg I) I); constructor
  apply inf_le_left
  exact h

  intro h
  obtain ⟨n, S, hS, hspan⟩ := h
  by_cases hzS : ∃ p ∈ S, p ≠ 0
  unfold IsSingleDegGen
  nth_rw 1 [hspan]; nth_rw 1 [hspan, minDeg_homo hzS hS]
  apply Submodule.span_eq_span

  apply le_trans ?_ Submodule.subset_span
  apply le_inf hS
  intro s hs; rw [Submodule.coe_restrictScalars, SetLike.mem_coe, hspan]
  apply (Ideal.subset_span) hs

  apply le_trans (inf_le_right)
  simp only [Submodule.coe_restrictScalars, Ideal.submodule_span_eq, Set.le_eq_subset,
    SetLike.coe_subset_coe]
  rw [hspan]


  push_neg at hzS
  have hSz : S ⊆ {0} := by exact hzS
  apply ideal_span_subset_zero_singleton at hSz
  rw [hspan, hSz]
  exact zero_singleDegGen

--theorem singleDegGen_iff' : IsSingleDegGen I ↔ ∃ S : Set (MvPolynomial α F), S ⊆ (homogeneousSubmodule α F (minDeg I) ) ∧ I = Ideal.span S := by sorry

theorem singleDegGen_of_symmSpan [DecidableEq α] {p : MvPolynomial α F} {n : ℕ} (h : p.IsHomogeneous n) : IsSingleDegGen (symmSpan {p}) := by
  rw [singleDegGen_iff]; use n; use symmSet {p}
  constructor
  exact symmSet_homo_singleton h
  rfl

theorem single_deg_gen_homo (h : IsSingleDegGen I) : Ideal.IsHomogeneous (homogeneousSubmodule α F) I := by
  apply (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule α F) I).mpr
  let n := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}
  let S := homogeneousSubmoduleI n I
  have hS : ∀ s ∈ S, s ∈ (SetLike.homogeneousSubmonoid (homogeneousSubmodule α F)) := by
    intro s hs; unfold S at hs
    apply Submonoid.mem_carrier.mp
    simp only [SetLike.homogeneousSubmonoid, Set.mem_setOf]
    apply Submodule.mem_inf.mp at hs; apply And.left at hs
    unfold SetLike.IsHomogeneousElem; use n
  let fs : S → (SetLike.homogeneousSubmonoid (homogeneousSubmodule α F)) := fun s => ⟨s, by exact hS s.1 s.2⟩
  use Set.range fs; rw [h]; congr

  ext p; constructor; intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right]
  rw [SetLike.mem_coe] at h
  use (hS p h); use p; use h

  intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right] at h
  rw [SetLike.mem_coe]
  obtain ⟨_, q, hp, hpq⟩ := h
  apply Subtype.mk_eq_mk.mp at hpq
  simp only at hpq
  rw [hpq] at hp
  exact hp

lemma homoSubI_strictMono (n : ℕ) {I J : Ideal (MvPolynomial α F)} (hmd : minDeg I = minDeg J) (hn : minDeg I = n)
  (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J): I < J → homogeneousSubmoduleI n I < homogeneousSubmoduleI n J := by
  intro hIJ
  apply lt_of_le_of_ne
  exact homoSubI_monotone n (le_of_lt hIJ)
  rw [← hn]; nth_rw 2 [hmd]
  rw [hI, hJ, lt_iff_le_and_ne] at hIJ
  apply And.right at hIJ
  contrapose! hIJ
  rw [hIJ]


variable [DecidableEq α]


@[simp] lemma homoSubI_span_apply {n m : ℕ} {S : Set (MvPolynomial α F)} (hnm : m ≥ n) (h : S ⊆ homogeneousSubmodule α F m) :
  homogeneousSubmoduleI n (Ideal.span S) = if n = m then homogeneousSubmoduleI m (Ideal.span S) else 0 := by
    by_cases heq : n = m
    rw [heq]; simp only [reduceIte]

    simp only [heq, reduceIte]
    apply (Submodule.eq_bot_iff (homogeneousSubmoduleI n (Ideal.span S))).mpr
    intro p hp
    by_cases hS : ∃ p ∈ S, p ≠ 0

    apply lt_of_le_of_ne hnm at heq
    apply minDeg_homo hS at h
    rw [← h] at heq
    apply Nat.notMem_of_lt_sInf at heq
    rw [Set.mem_setOf] at heq; push_neg at heq
    rw [heq] at hp
    exact hp

    push_neg at hS
    apply Ideal.span_eq_bot.mpr at hS
    rw [hS, ← Submodule.zero_eq_bot, homoSubI_zero] at hp
    exact hp

theorem homoSubI_span_eq {n : ℕ} {S : Set (MvPolynomial α F)} {f : ℕ → Set (MvPolynomial α F)}
  (hS : S = f n) (hf : ∀ i ≥ n, f i ⊆ homogeneousSubmodule α F i) (hfz : ∀ i < n, f i ⊆ {0}) :
  homogeneousSubmoduleI n (Ideal.span S) = homogeneousSubmoduleI n (Ideal.span (⋃ i, f i)) := by
    rw [Ideal.span_iUnion, homoSubI_iSup]; swap
    intro i
    by_cases hin : i < n
    let hI0 := ideal_span_subset_zero_singleton (hfz i hin)
    rw [hI0]
    apply Ideal.IsHomogeneous.bot

    push_neg at hin
    specialize hf i hin
    suffices IsSingleDegGen (Ideal.span (f i)) by exact single_deg_gen_homo this
    apply singleDegGen_iff.mpr; use i; use f i

    have hss : ∀ i, homogeneousSubmoduleI n (Ideal.span (f i)) = if n = i then homogeneousSubmoduleI i (Ideal.span (f i)) else 0 := by
      intro i
      by_cases hin : i ≥ n
      exact homoSubI_span_apply hin (hf i hin)
      push_neg at hin
      suffices Ideal.span (f i) = 0 by
        rw [this]
        let hn := Nat.ne_of_lt' hin
        simp only [hn, ↓reduceIte]
        exact homoSubI_zero
      exact ideal_span_subset_zero_singleton (hfz i hin)

    simp only [hss, Submodule.zero_eq_bot]
    rw [iSup_ite]
    simp only [iSup_iSup_eq_right, iSup_bot, bot_le, sup_of_le_left]
    rw [hS]


lemma psi_homo_gen_of_singleDegGen (hI : IsSingleDegGen I) (h : IsPrincipalSymmetric I) :
  ∃ f, f.IsHomogeneous (minDeg I) ∧ I = symmSpan {f} := by
    sorry
