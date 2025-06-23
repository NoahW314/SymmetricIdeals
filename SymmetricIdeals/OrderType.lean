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



lemma subset_homoOrderType {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} (hp : stronglyHomogeneous p a) :
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

lemma orderTypes_subset_add_eq_add {p₁ p₂ q₁ q₂ : MvPolynomial α F} (hp : Disjoint (orderTypes p₁) (orderTypes p₂))
  (hpq₁ : Disjoint (orderTypes p₁) (orderTypes q₁)) (hpq₂ : Disjoint (orderTypes p₂) (orderTypes q₂))
  (h : p₁ + q₁ = p₂ + q₂) : orderTypes p₁ ⊆ orderTypes q₂ := by
    suffices orderTypes p₁ ⊆ orderTypes p₂ ∪ orderTypes q₂ by
      exact Disjoint.subset_right_of_subset_union this hp
    calc orderTypes p₁
      _ ⊆ orderTypes p₁ ∪ orderTypes q₁ := by exact Set.subset_union_left
      _ = orderTypes (p₁+q₁) := by symm; exact orderTypes_add hpq₁
      _ = orderTypes (p₂+q₂) := by rw [h]
      _ = orderTypes p₂ ∪ orderTypes q₂ := by exact orderTypes_add hpq₂
