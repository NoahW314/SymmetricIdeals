import Mathlib
import SymmetricIdeals.Basic
import SymmetricIdeals.MinimalGenerating
import SymmetricIdeals.SingleDegGen

open MvPolynomial
open Equiv (Perm)

variable {F : Type*} [CommSemiring F]
variable {α : Type*}

def orderType (d : α →₀ ℕ) : Nat.Partition (d.degree) := ⟨
    Multiset.map d d.support.val,
    by
    intro i hi
    simp only [Multiset.mem_map, Finset.mem_val, Finsupp.mem_support_iff] at hi
    obtain ⟨a, haz, hai⟩ := hi
    rw [← hai]
    exact Nat.zero_lt_of_ne_zero haz
    ,
    by rw [Finsupp.degree, Finset.sum_map_val]⟩

--def orderType (d : α →₀ ℕ) := Multiset.map d d.support.val

/-
lemma exists_set_card {n : ℕ} (hα : n ≤ Nat.card α ∨ Infinite α) : ∃ p : Set α, Cardinal.mk ↑p = n := by
  rw [← Cardinal.le_mk_iff_exists_set]
  rcases hα with hα | hα

  suffices Nat.card α ≤ Cardinal.mk α by apply le_trans (Nat.cast_le.mpr hα) this
  by_cases h : (Nonempty (Finite α))
  obtain ⟨h⟩ := h
  apply le_of_eq
  exact Nat.cast_card

  suffices Nat.card α = 0 by rw [this]; apply zero_le
  suffices Infinite α by exact Nat.card_eq_zero_of_infinite
  refine not_finite_iff_infinite.mp ?_
  contrapose! h
  exact Nonempty.intro h

  apply le_trans ?_ (Cardinal.aleph0_le_mk α)
  apply le_of_lt (Cardinal.nat_lt_aleph0 n)

open Classical
lemma exists_mono_of_orderType {n : ℕ} (a : Nat.Partition n) (hα : a.parts.sizeOf ≤ Nat.card α ∨ Infinite α) :
  ∃ d : α →₀ ℕ, (orderType d).parts = a.parts := by
    obtain ⟨S, hcard⟩ := exists_set_card hα
    let L : List ℕ := Classical.choose (Quot.exists_rep a.parts)
    have hfS : Finite S := by
      refine Cardinal.mk_lt_aleph0_iff.mp ?_
      rw [hcard]
      exact Cardinal.nat_lt_aleph0 a.parts.sizeOf
    have hftS : Fintype S := by exact Set.Finite.fintype hfS
    obtain ⟨f, f', hlif, rif⟩ := hfS
    let supp := {x : S | L[(f x)]! ≠ 0}
    have hsuppFin : Fintype supp := by exact setFintype supp
    use ⟨supp.toFinset, fun x : α => if hx : x ∈ S then L[(f ⟨x, hx⟩)]! else 0,
      by
      simp only [Fin.getElem!_fin, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero, ne_eq,
        Set.toFinset_setOf, Finset.pure_def, Finset.bind_def, Finset.sup_singleton_apply,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists,
        exists_and_right, exists_eq_right, dite_eq_right_iff, not_forall, implies_true, supp]
      ⟩
    rw [← Classical.choose_spec (Quot.exists_rep a.parts)]
    simp [orderType, L]

    sorry

noncomputable
def partMono {n : ℕ} (a : Nat.Partition n) (hα : a.parts.sizeOf ≤ Nat.card α ∨ Infinite α) :=
  Classical.choose (exists_mono_of_orderType a hα)
-/


def stronglyHomogeneous {n : ℕ} (p : MvPolynomial α F) (a : Nat.Partition n) :=
  ∀ ⦃d⦄, coeff d p ≠ 0 → (orderType d).parts = a.parts


lemma isHomogeneous_of_stronglyHomogeneous {n : ℕ} {p : MvPolynomial α F} (a : Nat.Partition n) :
  stronglyHomogeneous p a → p.IsHomogeneous n := by
    intro h d hd
    specialize h hd
    let hd2 := (orderType d).parts_sum
    have hdd : (Finsupp.weight 1) d = d.degree := by
      simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
        LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
        id_eq, smul_eq_mul, mul_one, Finsupp.degree]
      rfl
    rw [hdd, ← hd2, ← a.parts_sum]
    exact congrArg Multiset.sum h

lemma sum_stronglyHomogeneous {n : ℕ} (a : Nat.Partition n) {p q : MvPolynomial α F} :
  stronglyHomogeneous p a → stronglyHomogeneous q a → stronglyHomogeneous (p+q) a := by
    intro hp hq
    simp_all only [stronglyHomogeneous, coeff_add]
    intro d hd
    have hpq : coeff d p ≠ 0 ∨ coeff d q ≠ 0 := by
      refine not_or_of_imp ?_
      intro hdp; rw [hdp, zero_add] at hd
      exact hd
    rcases hpq with hpz|hqz
    exact hp hpz
    exact hq hqz

lemma zero_stronglyHomogeneous {n : ℕ} (a : Nat.Partition n) : stronglyHomogeneous (0 : MvPolynomial α F) a := by
  simp only [stronglyHomogeneous, coeff_zero, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
    implies_true]

variable {F : Type*} [Field F]

lemma smul_stronglyHomogeneous {n : ℕ} (a : Nat.Partition n) (c : F) {p : MvPolynomial α F} :
  stronglyHomogeneous p a → stronglyHomogeneous (c • p) a := by
    by_cases hc : c = 0
    rw [hc, zero_smul]; intro hp
    exact zero_stronglyHomogeneous a

    simp only [stronglyHomogeneous, coeff_smul, smul_eq_mul]
    intro hp d hd
    apply (mul_ne_zero_iff_left hc).mp at hd
    exact hp hd

lemma stronglyHomogeneous_eq' {n m : ℕ} {a : Nat.Partition n} {b : Nat.Partition m}
  (h : a.parts = b.parts) {p : MvPolynomial α F} : stronglyHomogeneous p a → stronglyHomogeneous p b := by

    sorry

lemma stronglyHomogeneous_eq {n m : ℕ} {a : Nat.Partition n} {b : Nat.Partition m}
  (h : a.parts = b.parts) {p : MvPolynomial α F} : stronglyHomogeneous p a ↔ stronglyHomogeneous p b := by
    constructor; exact stronglyHomogeneous_eq' h
    symm at h; exact stronglyHomogeneous_eq' h


-- TODO: can we use orderType to place another grading on MvPolynomial?
def orderTypeComponent (α F : Type*) [Field F] {n : ℕ} (a : Nat.Partition n) : Submodule F (MvPolynomial α F) :=
  ⟨⟨⟨{p : MvPolynomial α F | stronglyHomogeneous p a}, by
    simp only [Set.mem_setOf_eq]; exact sum_stronglyHomogeneous a⟩, by
    simp only [Set.mem_setOf_eq]; exact zero_stronglyHomogeneous a⟩, by
    simp only [Set.mem_setOf_eq]; exact smul_stronglyHomogeneous a⟩

@[simp] lemma mem_orderTypeComponent {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} :
  p ∈ orderTypeComponent α F a ↔ stronglyHomogeneous p a := by
    simp only [orderTypeComponent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq]

lemma orderTypeComponent_eq {n m : ℕ} {a : Nat.Partition n} {b : Nat.Partition m}
  (h : a.parts = b.parts) : orderTypeComponent α F a = orderTypeComponent α F b := by
    ext p; rw [mem_orderTypeComponent, mem_orderTypeComponent]
    exact stronglyHomogeneous_eq h



lemma symm_parts (σ : Perm α) (d : α →₀ ℕ) : (orderType (Finsupp.mapDomain (⇑σ) d)).parts = (orderType d).parts := by
  simp only [orderType]
  let i : (x : α) → x ∈ (Finsupp.mapDomain (⇑σ) d).support.val → α := fun x hx => (Equiv.symm σ) x
  refine Multiset.map_eq_map_of_bij_of_nodup ⇑(Finsupp.mapDomain (⇑σ) d) ⇑d ?_ ?_ i ?_ ?_ ?_ ?_
  exact (Finsupp.mapDomain (⇑σ) d).support.nodup
  exact d.support.nodup

  intro x hx
  simp only [Finset.mem_val, Finsupp.mem_support_iff, i]
  simp only [Finset.mem_val, Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply] at hx
  exact hx

  intro x₁ hx₁ x₂ hx₂ hi
  unfold i at hi
  apply_fun σ at hi
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hi
  exact hi

  intro x hx; use σ x
  have hσx : σ x ∈ (Finsupp.mapDomain (⇑σ) d).support.val := by
    simp only [Finset.mem_val, Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply,
      Equiv.symm_apply_apply]
    simp only [Finset.mem_val, Finsupp.mem_support_iff] at hx
    exact hx
  use hσx; unfold i
  rw [Equiv.symm_apply_apply]

  intro x hx; unfold i
  rw [Finsupp.mapDomain_equiv_apply]

lemma stronglyHomogeneous_symm {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} (σ : Perm α) :
  stronglyHomogeneous p a → stronglyHomogeneous (σ • p) a := by
    intro h d hd
    apply coeff_rename_ne_zero at hd
    obtain ⟨u, hud, hu⟩ := hd
    specialize h hu
    rw [← hud, ← h]
    exact symm_parts σ u

lemma orderTypeComponent_symm {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} (σ : Perm α) :
  p ∈ orderTypeComponent α F a → σ • p ∈ orderTypeComponent α F a := by
    rw [mem_orderTypeComponent, mem_orderTypeComponent]
    exact stronglyHomogeneous_symm σ



lemma subset_orderTypeComponent {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} (hp : stronglyHomogeneous p a) :
  symmSpan {p} ≤ Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F)) := by
    unfold symmSpan
    apply Ideal.span_le.mpr
    apply le_trans ?_ (Ideal.subset_span)

    intro q hq
    rw [← mem_orderTypeComponent] at hp
    rw [mem_symmSet_singleton] at hq
    obtain ⟨σ, hq⟩ := hq
    rw [← hq]
    exact orderTypeComponent_symm σ hp

lemma orderTypeComponent_subset_homoSub {n : ℕ} (a : Nat.Partition n) :
  ((orderTypeComponent α F a) : Set (MvPolynomial α F)) ⊆ ↑(homogeneousSubmodule α F n) := by
    intro q
    simp only [SetLike.mem_coe, mem_orderTypeComponent, mem_homogeneousSubmodule]
    exact isHomogeneous_of_stronglyHomogeneous a

variable [DecidableEq α]

lemma minDeg_orderTypeComponent {n : ℕ} {a : Nat.Partition n} (h : ∃ p ∈ (orderTypeComponent α F a), p ≠ 0) :
  minDeg (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) = n := by
    apply minDeg_homo h (orderTypeComponent_subset_homoSub a)

lemma homoSubI_orderTypeComponent {n : ℕ} (a : Nat.Partition n) :
  homogeneousSubmoduleI (minDeg (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))))
  (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) = orderTypeComponent α F a := by
    by_cases hp : ∃ p ∈ (orderTypeComponent α F a), p ≠ 0
    rw [minDeg_orderTypeComponent hp]
    rw [homoSubI_span n ((orderTypeComponent α F a) : Set (MvPolynomial α F)) (orderTypeComponent_subset_homoSub a)]
    exact Submodule.span_eq (orderTypeComponent α F a)

    push_neg at hp
    apply (Submodule.eq_bot_iff _).mpr at hp
    rw [hp]
    simp only [Submodule.bot_coe, subset_refl, ideal_span_subset_zero_singleton,
      Submodule.zero_eq_bot, minDeg_bot]
    rw [← Submodule.zero_eq_bot, ← Submodule.zero_eq_bot, homoSubI_zero]

lemma singleDegGen_orderTypeComponent {n : ℕ} (a : Nat.Partition n) : IsSingleDegGen (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
  apply singleDegGen_iff.mpr
  use n; use orderTypeComponent α F a; constructor
  exact orderTypeComponent_subset_homoSub a
  rfl


lemma monomials_basis_orderTypeComponent {n : ℕ} {a : Nat.Partition n} :
  orderTypeComponent α F a = Submodule.span F ((fun d => (monomial d (1 : F)))
  '' {d : α →₀ ℕ | stronglyHomogeneous (monomial d (1 : F)) a}) := by

    sorry

lemma exists_perm_of_monomial (d e : α →₀ ℕ) (h : (orderType d).parts = (orderType e).parts) :
∃ σ : Equiv.Perm α, Finsupp.mapDomain σ d = e := by

  sorry

def monomial_symmSpan_is_orderTypeComponent (p : MvPolynomial α F) := ∃ d : α →₀ ℕ, p = monomial d (1 : F) ∧
  symmSpan {monomial d (1 : F)} = Ideal.span (orderTypeComponent α F (orderType d))

lemma monomial_symmSpan_orderTypeComponent' (d : α →₀ ℕ) (c : F) : monomial_symmSpan_is_orderTypeComponent (monomial d c) := by
  apply induction_on_monomial
  sorry
  sorry

lemma monomial_symmSpan_orderTypeComponent {n : ℕ} {a : Nat.Partition n} {d : α →₀ ℕ}
  (h : stronglyHomogeneous (monomial d (1 : F)) a) :
  symmSpan {monomial d (1 : F)} = Ideal.span (orderTypeComponent α F a) := by
    /-apply antisymm (subset_orderTypeComponent h)
    rw [Ideal.span, Submodule.span_le, monomials_basis_orderTypeComponent, symmSpan,
      Ideal.span]
    suffices Submodule.span F ((fun d => (monomial d (1 : F))) '' {d : α →₀ ℕ | stronglyHomogeneous (monomial d (1 : F)) a}) ≤ Submodule.span F (symmSet {monomial d (1 : F)}) by
      apply subset_trans this
      apply Submodule.span_le_restrictScalars
    apply Submodule.span_mono
    intro m;
    simp only [Set.mem_image, Set.mem_setOf_eq, mem_symmSet_singleton,
      forall_exists_index, and_imp, symm_monomial]
    intro e hmsh hem
    rw [← hem];
    --let σ : Equiv.Perm α := ⟨fun x : α => , sorry, sorry, sorry⟩
    sorry-/

    obtain ⟨e, hed, hspan⟩ := monomial_symmSpan_orderTypeComponent' d (1 : F)
    apply monomial_left_injective (one_ne_zero) at hed;
    rw [hed, hspan, ← hed]; congr
    sorry

lemma exists_monomial_symmSpan_orderTypeComponent {n : ℕ} {a : Nat.Partition n}
  (h : ∃ p : MvPolynomial α F, p ≠ 0 ∧ stronglyHomogeneous p a) :
  ∃ d : α →₀ ℕ, symmSpan {monomial d (1 : F)} = Ideal.span (orderTypeComponent α F a) := by
    obtain ⟨p, hpz, hpsh⟩ := h
    rw [MvPolynomial.ne_zero_iff] at hpz
    obtain ⟨d, hpd⟩ := hpz
    have hd : stronglyHomogeneous (monomial d (1 : F)) a := by
      intro e he
      simp only [coeff_monomial, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        Decidable.not_not] at he
      rw [← he]
      exact hpsh hpd
    use d
    exact monomial_symmSpan_orderTypeComponent hd

lemma psi_orderTypeComponent' {n : ℕ} {a : Nat.Partition n} :
  (∃ (p : MvPolynomial α F), p ≠ 0 ∧ stronglyHomogeneous p a) →
  IsPrincipalSymmetric (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
    intro h
    apply exists_monomial_symmSpan_orderTypeComponent at h
    obtain ⟨d, h⟩ := h
    use (monomial d (1 : F)); symm
    exact h

lemma psi_orderTypeComponent {n : ℕ} (a : Nat.Partition n) :
  IsPrincipalSymmetric (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
    by_cases h : ∃ p : MvPolynomial α F, p ≠ 0 ∧ stronglyHomogeneous p a
    exact psi_orderTypeComponent' h
    push_neg at h
    suffices orderTypeComponent α F a = ⊥ by
      rw [this]
      simp only [Submodule.bot_coe, subset_refl, ideal_span_subset_zero_singleton,
        Submodule.zero_eq_bot]
      exact bot_is_psi
    rw [Submodule.eq_bot_iff]
    intro p; specialize h p
    rw [mem_orderTypeComponent]; contrapose!
    exact h

section DisjointOrderTypes

omit [DecidableEq α]

def orderTypes (p : MvPolynomial α F) := (fun d => (orderType d).parts) '' {d : α →₀ ℕ | coeff d p ≠ 0}

lemma mem_orderTypes {p : MvPolynomial α F} {d : α →₀ ℕ} : coeff d p ≠ 0 → (orderType d).parts ∈ orderTypes p := by
  simp only [ne_eq, orderTypes, Set.mem_image, Set.mem_setOf_eq]
  intro h; use d

lemma orderTypes_disjoint_iff {p q : MvPolynomial α F} : Disjoint (orderTypes p) (orderTypes q) ↔ ∀ d e : α →₀ ℕ,
  coeff d p ≠ 0 → coeff e q ≠ 0 → (orderType d).parts ≠ (orderType e).parts := by
    constructor; intro h d e hd he
    contrapose! h
    refine Set.not_disjoint_iff.mpr ?_
    use (orderType d).parts; constructor
    apply mem_orderTypes hd
    rw [h]; apply mem_orderTypes he

    contrapose!
    intro h
    apply Set.not_disjoint_iff.mp at h
    obtain ⟨f, hop, hoq⟩ := h
    simp only [orderTypes, Set.mem_image, Set.mem_setOf_eq] at hop
    simp only [orderTypes, Set.mem_image, Set.mem_setOf_eq] at hoq
    obtain ⟨d, hd⟩ := hop
    obtain ⟨e, he⟩ := hoq
    use d; use e; constructor; exact hd.1; constructor; exact he.1
    rw [hd.2, he.2]

lemma orderTypes_sub_subset {p q : MvPolynomial α F} (h : orderTypes p ⊆ orderTypes q) : orderTypes (q-p) ⊆ orderTypes q := by
  intro s hs
  simp only [orderTypes, coeff_sub, ne_eq, Set.mem_image, Set.mem_setOf_eq] at hs
  obtain ⟨d, hdpq, hs⟩ := hs
  by_cases hd : coeff d p = 0
  use d; constructor;
  rw [Set.mem_setOf]
  rw [hd, sub_zero] at hdpq
  exact hdpq
  exact hs

  apply mem_orderTypes at hd
  rw [hs] at hd
  exact h hd

lemma orderTypes_disjoint_sub {p q r : MvPolynomial α F} (hpq : Disjoint (orderTypes p) (orderTypes q))
  (hqr : orderTypes r ⊆ orderTypes q) : Disjoint (orderTypes p) (orderTypes (q-r)) := by
    apply orderTypes_sub_subset at hqr
    apply Set.disjoint_of_subset_right hqr hpq

lemma orderTypes_add_subset {p q : MvPolynomial α F} : orderTypes (p+q) ⊆ orderTypes p ∪ orderTypes q := by
  intro s
  simp only [orderTypes, coeff_add, ne_eq, Set.mem_image, Set.mem_setOf_eq, Set.mem_union,
    forall_exists_index, and_imp]
  intro d hdc hds
  by_cases hdz : coeff d p ≠ 0
  left; use d

  push_neg at hdz
  rw [hdz, zero_add] at hdc
  right; use d

lemma orderTypes_sum_subset {X : Type*} {s : Finset X} {f : X → MvPolynomial α F} :
  orderTypes (∑ x ∈ s, f x) ⊆ ⋃ x ∈ s, orderTypes (f x) := by
    simp only [orderTypes, ne_eq, Set.image_subset_iff, Set.preimage_iUnion]
    intro d hd; rw [Set.mem_setOf, coeff_sum] at hd
    push_neg at hd
    apply Finset.exists_ne_zero_of_sum_ne_zero at hd
    obtain ⟨i, his, hi⟩ := hd
    rw [Set.mem_iUnion₂]; use i; use his
    apply Set.subset_preimage_image; rw [Set.mem_setOf]
    exact hi

lemma orderTypes_add {p q : MvPolynomial α F} (h : Disjoint (orderTypes p) (orderTypes q)) :
  orderTypes (p+q) = orderTypes p ∪ orderTypes q := by
    apply antisymm orderTypes_add_subset
    intro s hs
    rw [Set.mem_union] at hs
    wlog hsp : s ∈ orderTypes p
    rw [disjoint_comm] at h; rw [Or.comm] at hs
    rw [add_comm]
    apply this h hs
    simp only [hsp, or_false] at hs
    exact hs

    have hsq : s ∉ orderTypes q := by exact Disjoint.notMem_of_mem_left h hsp
    simp only [orderTypes, coeff_add, ne_eq, Set.mem_image, Set.mem_setOf_eq]
    simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq] at hsp
    obtain ⟨d, hdp, hds⟩ := hsp
    use d; constructor; swap; exact hds
    contrapose! hsq
    rw [← hds]; apply mem_orderTypes
    contrapose! hsq
    rw [hsq, add_zero]; exact hdp

lemma orderTypes_subset_of_add_eq_add {p₁ p₂ q₁ q₂ : MvPolynomial α F} (hp : Disjoint (orderTypes p₁) (orderTypes p₂))
  (hpq₁ : Disjoint (orderTypes p₁) (orderTypes q₁)) (hpq₂ : Disjoint (orderTypes p₂) (orderTypes q₂))
  (h : p₁ + q₁ = p₂ + q₂) : orderTypes p₁ ⊆ orderTypes q₂ := by
    suffices orderTypes p₁ ⊆ orderTypes p₂ ∪ orderTypes q₂ by
      exact Disjoint.subset_right_of_subset_union this hp
    calc orderTypes p₁
      _ ⊆ orderTypes p₁ ∪ orderTypes q₁ := by exact Set.subset_union_left
      _ = orderTypes (p₁+q₁) := by symm; exact orderTypes_add hpq₁
      _ = orderTypes (p₂+q₂) := by rw [h]
      _ = orderTypes p₂ ∪ orderTypes q₂ := by exact orderTypes_add hpq₂

@[simp] lemma orderTypes_zero : orderTypes (0 : MvPolynomial α F) = ∅ := by
  simp only [orderTypes, coeff_zero, ne_eq, not_true_eq_false, Set.setOf_false, Set.image_empty]

@[simp] lemma orderTypes_C_mul_ne_zero {p : MvPolynomial α F} {c : F} (h : c ≠ 0) : orderTypes (c • p) = orderTypes p := by
  simp only [orderTypes, coeff_smul, smul_eq_mul, ne_eq, mul_eq_zero, h, false_or]
lemma orderTypes_C_mul {p : MvPolynomial α F} {c : F} : orderTypes (c • p) ⊆ orderTypes p := by
  by_cases h : c ≠ 0
  rw [orderTypes_C_mul_ne_zero h]
  push_neg at h; rw [h, zero_smul, orderTypes_zero]
  exact Set.empty_subset (orderTypes p)

@[simp] lemma orderTypes_minus (p : MvPolynomial α F) : orderTypes (-p) = orderTypes p := by
  simp only [orderTypes, coeff_neg, ne_eq, neg_eq_zero]

lemma orderTypes_disjoint_add {p q₁ q₂ : MvPolynomial α F} (h1 : Disjoint (orderTypes p) (orderTypes q₁))
  (h2 : Disjoint (orderTypes p) (orderTypes q₂)) : Disjoint (orderTypes p) (orderTypes (q₁+q₂)) := by
    apply Disjoint.mono_right (orderTypes_add_subset)
    exact Disjoint.union_right h1 h2

lemma disjoint_sub_orderTypes_of_add_eq_add {p₁ p₂ q₁ q₂ : MvPolynomial α F} (hp : Disjoint (orderTypes p₁) (orderTypes p₂))
  (hpq₁ : Disjoint (orderTypes p₁) (orderTypes q₁)) (h : p₁ + q₁ = p₂ + q₂) :
  Disjoint (orderTypes p₁) (orderTypes (q₂-p₁)) := by
    suffices q₂-p₁ = q₁+(-p₂) by
      rw [this]
      rw [← orderTypes_minus p₂] at hp
      exact orderTypes_disjoint_add hpq₁ hp
    symm at h
    rw [add_comm, ← eq_add_neg_iff_add_eq] at h
    rw [h]; ring

lemma orderTypes_symm_subset {p : MvPolynomial α F} {σ : Perm α} : orderTypes (σ • p) ⊆ orderTypes p := by
  intro s; simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq]
  intro h
  obtain ⟨d, hd, hds⟩ := h
  apply coeff_rename_ne_zero at hd
  obtain ⟨e, hed, he⟩ := hd
  use e; constructor; exact he
  rw [← hds, ← hed]; symm
  exact symm_parts σ e

lemma orderTypes_symm {p : MvPolynomial α F} {σ : Perm α} : orderTypes (σ • p) = orderTypes p := by
  apply antisymm orderTypes_symm_subset
  have hps : p = σ.symm • (σ • p) := by exact inv_smul_eq_iff.mp rfl
  nth_rw 1 [hps]
  exact orderTypes_symm_subset

lemma orderTypes_symmSet {p q : MvPolynomial α F} (h : q ∈ symmSet {p}) : orderTypes q = orderTypes p := by
  rw [mem_symmSet_singleton] at h
  obtain ⟨σ, h⟩ := h
  rw [← h]
  exact orderTypes_symm

lemma empty_orderTypes_iff_zero {p : MvPolynomial α F} : orderTypes p = ∅ ↔ p = 0 := by
  constructor; contrapose!; intro h
  rw [ne_eq, eq_zero_iff.not] at h
  push_neg at h
  obtain ⟨d, h⟩ := h
  use (orderType d).parts
  exact mem_orderTypes h

  intro h; rw [h]; exact orderTypes_zero

lemma empty_orderTypes_of_disjoint_add {f p q : MvPolynomial α F} (h : f = p + q) (hpq : Disjoint (orderTypes f) (orderTypes q))
  (hpq' : Disjoint (orderTypes p) (orderTypes q)) : orderTypes q = ∅ := by
    have hasd : orderTypes q ⊆ orderTypes f := by
      rw [h, orderTypes_add hpq']
      exact Set.subset_union_right
    exact Set.subset_empty_iff.mp (hpq hasd fun ⦃a⦄ a ↦ a)

lemma zero_of_disjoint_add {f p q : MvPolynomial α F} (h : f = p + q) (hpq : Disjoint (orderTypes f) (orderTypes q))
  (hpq' : Disjoint (orderTypes p) (orderTypes q)) : q = 0 := by
    rw [← empty_orderTypes_iff_zero]
    exact empty_orderTypes_of_disjoint_add h hpq hpq'

lemma zero_of_disjoint_sum {p : MvPolynomial α F} {r : ℕ} {q : Fin r → MvPolynomial α F}
  (hsum : p = ∑ i, q i) (hdot : ∀ i j : Fin r, i ≠ j → Disjoint (orderTypes (q i)) (orderTypes (q j)))
  (i₀ : Fin r) (hq : ∀ i : Fin r, i ≠ i₀ → Disjoint (orderTypes (q i)) (orderTypes p)) :
  ∀ i ≠ i₀, q i = 0 := by
    intro i hi
    have hpe : p = (∑ j ∈ Finset.univ.erase i, q j) + (q i) := by
      simp only [Finset.mem_univ, Finset.sum_erase_eq_sub, sub_add_cancel]
      exact hsum
    apply zero_of_disjoint_add hpe
    rw [disjoint_comm]
    exact hq i hi
    apply Disjoint.mono_left orderTypes_sum_subset
    apply Set.disjoint_iUnion₂_left.mpr
    intro j hj
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hj
    exact hdot j i hj
