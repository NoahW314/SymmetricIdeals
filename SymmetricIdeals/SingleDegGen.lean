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


theorem singleDegGen_iff' [DecidableEq α] : IsSingleDegGen I ↔ ∃ S : Set (MvPolynomial α F), S ⊆ (homogeneousSubmodule α F (minDeg I) ) ∧ I = Ideal.span S := by
  constructor; intro h
  rw [singleDegGen_iff] at h
  obtain ⟨n, S, h⟩ := h; use S; constructor
  swap; exact h.2

  by_cases hS : ∃ p ∈ S, p ≠ 0
  let hn := minDeg_homo hS h.1
  rw [h.2, hn]; exact h.1

  push_neg at hS
  let hIB := Ideal.span_eq_bot.mpr hS
  rw [← h.2] at hIB
  rw [hIB, minDeg_bot]
  intro p hp; apply hS p at hp; rw [hp]
  simp only [SetLike.mem_coe, Submodule.zero_mem]

  intro h; rw [singleDegGen_iff]; use minDeg I

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

lemma eq_of_minDeg_homoSubI_eq {I J : Ideal (MvPolynomial α F)}
  (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J) :
  homogeneousSubmoduleI (minDeg I) I = homogeneousSubmoduleI (minDeg J) J → I = J := by
    intro h
    rw [hI, hJ, h]

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

open Classical
theorem homoComps_gen_singleDegGen_ideal {I : Ideal (MvPolynomial α F)} {S : Set (MvPolynomial α F)}
  (h : IsSingleDegGen I) (hspan : I = Ideal.span S) :
  homogeneousSubmoduleI (minDeg I) I ≤ homogeneousSubmoduleI (minDeg I)
  (Ideal.span ((homogeneousComponent (minDeg I)) '' S)) := by
    let Sa := ⋃ i : ℕ, (homogeneousComponent i) '' S
    have hsas : homogeneousSubmoduleI (minDeg I) (Ideal.span ((homogeneousComponent (minDeg I)) '' S))
    = homogeneousSubmoduleI (minDeg I) (Ideal.span Sa) := by
      apply homoSubI_span_eq
      rfl

      intro i hi p hp
      simp only [SetLike.mem_coe, mem_homogeneousSubmodule]
      obtain ⟨q, hqS, hq⟩ := hp
      rw [← hq]
      exact homogeneousComponent_isHomogeneous i q

      intro i hi p hp
      obtain ⟨q, hqS, hq⟩ := hp
      rw [Set.mem_singleton_iff]
      apply Nat.notMem_of_lt_sInf at hi; rw [Set.mem_setOf] at hi; push_neg at hi
      suffices p ∈ homogeneousSubmoduleI i I by
        rw [hi] at this
        exact this
      unfold homogeneousSubmoduleI
      rw [← hq, Submodule.mem_inf]; constructor
      exact homogeneousComponent_mem i q
      rw [Submodule.restrictScalars_mem]
      apply single_deg_gen_homo at h
      suffices q ∈ I by
        specialize h i this
        have hd : (DirectSum.decompose (homogeneousSubmodule α F)) q = DirectSum.Decomposition.decompose' q := by rfl
        rw [hd, decomposition.decompose'_apply] at h
        exact h
      rw [hspan]
      apply Submodule.subset_span; exact hqS

    rw [hsas]
    suffices I ≤ Ideal.span Sa by apply homoSubI_monotone (minDeg I) this

    rw [hspan]
    apply Submodule.span_le.mpr
    intro p hp
    apply Submodule.mem_span_set.mpr
    have hps := sum_homogeneousComponent p
    have hhcp : Fintype (Set.range (homogeneousComponent . p)) := by
      let f : Finset.range (p.totalDegree + 2) → (Set.range (homogeneousComponent . p)) := fun i =>
        ⟨homogeneousComponent i p, by rw [Set.mem_range]; use i⟩
      apply Fintype.ofSurjective f
      intro q; let hq := q.2
      rw [Set.mem_range] at hq
      obtain ⟨i, hq⟩ := hq

      by_cases hi : i ∈ Finset.range (p.totalDegree + 2)
      use ⟨i, hi⟩; unfold f;
      apply Subtype.mk_eq_mk.mpr; rw [Subtype.coe_mk]
      exact hq

      use ⟨p.totalDegree+1, by
        apply Finset.mem_range.mpr
        exact Nat.lt_add_one (p.totalDegree + 1)⟩
      unfold f; apply Subtype.mk_eq_mk.mpr; rw [Subtype.coe_mk]
      rw [homogeneousComponent_eq_zero]
      rw [← hq]; symm
      apply homogeneousComponent_eq_zero
      apply Finset.mem_range.not.mp at hi; push_neg at hi
      apply lt_of_lt_of_le ?_ hi
      exact Nat.lt_add_of_pos_right (zero_lt_two)
      exact lt_add_one p.totalDegree
    let c : MvPolynomial α F →₀ MvPolynomial α F := ⟨(Set.range (homogeneousComponent . p)).toFinset,
      fun q => if q ∈ Set.range (homogeneousComponent . p) then 1 else 0, by
        simp only [Set.mem_toFinset, Set.mem_range, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
          not_exists, not_forall, Decidable.not_not, implies_true]
      ⟩
    use c; constructor
    simp only [Set.coe_toFinset, c]
    intro q hq
    rw [Set.mem_range] at hq
    obtain ⟨i, hq⟩ := hq; unfold Sa
    rw [← hq, Set.mem_iUnion]
    use i; rw [Set.mem_image]; use p

    unfold Finsupp.sum; rw [← hps]; symm
    let e : (i : ℕ) → (i ∈ Finset.range (p.totalDegree +1)) → ((homogeneousComponent . p) i ≠ 0) → MvPolynomial α F :=
      fun i hi hcz => (homogeneousComponent i) p
    apply Finset.sum_bij_ne_zero e

    intro i h₁ h₂
    simp only [Set.mem_toFinset, Set.mem_range, c, e]; use i

    intro i h₁₁ h₁₂ j h₂₁ h₂₂ he
    unfold e at he
    have hi : ((homogeneousComponent i) p).IsHomogeneous i := by exact homogeneousComponent_isHomogeneous i p
    have hj : ((homogeneousComponent j) p).IsHomogeneous j := by exact homogeneousComponent_isHomogeneous j p
    rw [he] at hi
    apply IsHomogeneous.inj_right hi hj h₂₂

    intro b hb hbz
    simp only [smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hbz
    have hcb : c b ≠ 0 := by exact Finsupp.mem_support_iff.mp hb
    simp only [hcb, not_false_eq_true, true_and] at hbz
    simp only [Set.mem_toFinset, Set.mem_range, c] at hb
    obtain ⟨i, hb⟩ := hb; use i
    rw [← hb] at hbz
    have hifr : i ∈ Finset.range (p.totalDegree + 1) := by
      contrapose! hbz
      apply homogeneousComponent_eq_zero
      rw [Finset.mem_range.not] at hbz; push_neg at hbz
      exact hbz
    use hifr; use hbz

    intro i h₁ h₂
    simp [smul_eq_mul, c, e]

lemma psi_homo_gen_of_singleDegGen (hI : IsSingleDegGen I) (h : IsPrincipalSymmetric I) :
  ∃ f, f.IsHomogeneous (minDeg I) ∧ I = symmSpan {f} := by
    obtain ⟨f, h⟩ := h
    let hIh := single_deg_gen_homo hI
    by_cases hmd0 : minDeg I = 0
    let hmd1 := (minDeg_zero_iff hIh).mp hmd0
    rcases hmd1 with hIT|hIB
    use 1; constructor; rw [hmd0]
    exact isHomogeneous_one α F
    rw [symmSpan_one, hIT]

    use 0; constructor; rw [hmd0]
    exact isHomogeneous_zero α F 0
    rw [symmSpan_zero, hIB]


    apply minDeg_mem at hmd0; rw [Set.mem_setOf] at hmd0
    use (homogeneousComponent (minDeg I) f); constructor
    exact homogeneousComponent_isHomogeneous (minDeg I) f
    have hssI : symmSpan {homogeneousComponent (minDeg I) f} ≤ I := by
      unfold symmSpan
      apply Submodule.span_le.mpr
      intro f' hf
      rw [mem_symmSet_singleton] at hf
      obtain ⟨σ, hf⟩ := hf
      rw [h, ← hf]
      apply symmSpan_symm
      rw [← h]
      apply single_deg_gen_homo at hI
      have hfI : f ∈ I := by rw [h]; exact mem_symmSpan_self
      specialize hI (minDeg I) hfI
      have hfdd : DirectSum.decompose (homogeneousSubmodule α F) f = DirectSum.Decomposition.decompose' f := by rfl
      rw [hfdd] at hI
      rw [decomposition.decompose'_apply] at hI
      exact hI
    suffices homogeneousSubmoduleI (minDeg I) I = homogeneousSubmoduleI (minDeg I) (symmSpan {(homogeneousComponent (minDeg I)) f}) by
      have hss :=  singleDegGen_of_symmSpan (homogeneousComponent_isHomogeneous (minDeg I) f)
      apply eq_of_minDeg_homoSubI_eq hI hss
      rw [this]; congr 1
      have hfz : homogeneousComponent (minDeg I) f ≠ 0 := by
        contrapose! hmd0
        rw [this, hmd0, symmSpan_zero, ← Submodule.zero_eq_bot, homoSubI_zero,
          Submodule.zero_eq_bot]

      rw [symmSpan, minDeg_homo]
      use homogeneousComponent (minDeg I) f; constructor
      exact mem_symmSet_singleton_self
      exact hfz
      exact symmSet_homo_singleton (homogeneousComponent_isHomogeneous (minDeg I) f)

    suffices homogeneousSubmoduleI (minDeg I) I ≥ homogeneousSubmoduleI (minDeg I)
      (symmSpan {(homogeneousComponent (minDeg I)) f}) by
        apply antisymm this
        suffices ⇑(homogeneousComponent (minDeg I)) '' symmSet {f} = symmSet {(homogeneousComponent (minDeg I)) f} by
          rw [symmSpan, ← this]
          exact homoComps_gen_singleDegGen_ideal hI h
        ext p;
        simp only [Set.mem_image, mem_symmSet_singleton, exists_exists_eq_and, homoComp_symmAct]

    apply homoSubI_monotone (minDeg I) hssI


omit [DecidableEq α] in
lemma homoSpan_mul {I J : Ideal (MvPolynomial α F)} {n m : ℕ} {S T : Set (MvPolynomial α F)}
  (hI : S ⊆ (homogeneousSubmodule α F n) ∧ I = Ideal.span S) (hJ : T ⊆ (homogeneousSubmodule α F m) ∧ J = Ideal.span T) :
  Set.mul.mul S T ⊆ (homogeneousSubmodule α F (n+m)) ∧ I*J = Ideal.span (Set.mul.mul S T) := by
    constructor
    intro r hr
    apply Set.mem_mul.mp at hr
    obtain ⟨p, hp, q, hq, hr⟩ := hr
    apply hI.1 at hp; apply hJ.1 at hq
    rw [SetLike.mem_coe, mem_homogeneousSubmodule] at hp
    rw [SetLike.mem_coe, mem_homogeneousSubmodule] at hq
    rw [← hr, SetLike.mem_coe, mem_homogeneousSubmodule]
    exact IsHomogeneous.mul hp hq

    rw [hI.2, hJ.2]
    apply Ideal.span_mul_span'

lemma singleDegGen_mul {I J : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I)
  (hJ : IsSingleDegGen J) : IsSingleDegGen (I*J) := by
  rw [singleDegGen_iff] at hI; rw [singleDegGen_iff] at hJ
  obtain ⟨n, S, hI⟩ := hI; obtain ⟨m, T, hJ⟩ := hJ
  rw [singleDegGen_iff]
  use n+m; use Set.mul.mul S T
  exact homoSpan_mul hI hJ
