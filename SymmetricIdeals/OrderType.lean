import Mathlib
import SymmetricIdeals.Basic
import SymmetricIdeals.MinimalGenerating
import SymmetricIdeals.SingleDegGen

open MvPolynomial
open Equiv (Perm)

variable {F : Type*} [CommSemiring F]
variable {α : Type*}


def orderType (d : α →₀ ℕ) := Multiset.map d d.support.val

@[simp] lemma orderType_zero : orderType (0 : α →₀ ℕ) = ∅ := by
  simp only [orderType, Finsupp.support_zero, Finset.empty_val, Finsupp.coe_zero, Pi.zero_apply,
    Multiset.map_zero, Multiset.empty_eq_zero]

lemma orderType_empty_iff {d : α →₀ ℕ} : orderType d = ∅ ↔ d = 0 := by
  constructor;
  simp only [orderType, Multiset.empty_eq_zero, Multiset.map_eq_zero, Finset.val_eq_zero,
    Finsupp.support_eq_empty, imp_self]
  intro h; rw [h]; exact orderType_zero




def stronglyHomogeneous (p : MvPolynomial α F) (a : Multiset ℕ) :=
  ∀ ⦃d⦄, coeff d p ≠ 0 → (orderType d) = a

lemma stronglyHomogeneous_constant [DecidableEq α] {c : F} : stronglyHomogeneous (C c : MvPolynomial α F) ∅ := by
  simp only [stronglyHomogeneous, coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp,
    Multiset.empty_eq_zero, and_imp, forall_eq', orderType_zero, implies_true]

@[simp] lemma stronglyHomogeneous_one [DecidableEq α] : stronglyHomogeneous (1 : MvPolynomial α F) 0 := by
  apply stronglyHomogeneous_constant

lemma stronglyHomogeneous_empty_iff [DecidableEq α] {p : MvPolynomial α F} : stronglyHomogeneous p ∅ ↔ ∃ c : F, p = C c := by
  constructor;
  intro h; unfold stronglyHomogeneous at h
  use coeff 0 p
  ext d; rw [coeff_C]
  by_cases hd : 0 = d
  simp only [hd, ↓reduceIte]
  simp only [hd, ↓reduceIte]
  contrapose! h; use d; constructor; exact h
  contrapose! hd; symm
  exact orderType_empty_iff.mp hd

  intro h; obtain ⟨c, h⟩ := h
  rw [h]; exact stronglyHomogeneous_constant



lemma orderType_sum_eq_degree {d : α →₀ ℕ} : (orderType d).sum = d.degree := by
  simp only [orderType, Finset.sum_map_val, Finsupp.degree]

lemma degree_eq_finsupp_weight_one {d : α →₀ ℕ} : (Finsupp.weight 1) d = d.degree := by
  simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
        LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
        id_eq, smul_eq_mul, mul_one, Finsupp.degree]
  rfl

lemma isHomogeneous_of_stronglyHomogeneous {p : MvPolynomial α F} (a : Multiset ℕ) :
  stronglyHomogeneous p a → p.IsHomogeneous (Multiset.sum a) := by
    intro h d hd
    specialize h hd
    have hdd : (Finsupp.weight 1) d = d.degree := by exact degree_eq_finsupp_weight_one
    rw [← h, orderType_sum_eq_degree, hdd]

lemma sum_stronglyHomogeneous (a : Multiset ℕ) {p q : MvPolynomial α F} :
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

lemma zero_stronglyHomogeneous (a : Multiset ℕ) : stronglyHomogeneous (0 : MvPolynomial α F) a := by
  simp only [stronglyHomogeneous, coeff_zero, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
    implies_true]

variable {F : Type*} [Field F]

lemma smul_stronglyHomogeneous (a : Multiset ℕ) (c : F) {p : MvPolynomial α F} :
  stronglyHomogeneous p a → stronglyHomogeneous (c • p) a := by
    by_cases hc : c = 0
    rw [hc, zero_smul]; intro hp
    exact zero_stronglyHomogeneous a

    simp only [stronglyHomogeneous, coeff_smul, smul_eq_mul]
    intro hp d hd
    apply (mul_ne_zero_iff_left hc).mp at hd
    exact hp hd

-- TODO: can we use orderType to place another grading on MvPolynomial?
def orderTypeComponent (α F : Type*) [Field F] (a : Multiset ℕ) : Submodule F (MvPolynomial α F) :=
  ⟨⟨⟨{p : MvPolynomial α F | stronglyHomogeneous p a}, by
    simp only [Set.mem_setOf_eq]; exact sum_stronglyHomogeneous a⟩, by
    simp only [Set.mem_setOf_eq]; exact zero_stronglyHomogeneous a⟩, by
    simp only [Set.mem_setOf_eq]; exact smul_stronglyHomogeneous a⟩

@[simp] lemma mem_orderTypeComponent {p : MvPolynomial α F} {a : Multiset ℕ} :
  p ∈ orderTypeComponent α F a ↔ stronglyHomogeneous p a := by
    simp only [orderTypeComponent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq]


lemma symm_orderType (σ : Perm α) (d : α →₀ ℕ) : orderType (Finsupp.mapDomain (⇑σ) d) = orderType d := by
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

lemma stronglyHomogeneous_symm {p : MvPolynomial α F} {a : Multiset ℕ} (σ : Perm α) :
  stronglyHomogeneous p a → stronglyHomogeneous (σ • p) a := by
    intro h d hd
    apply coeff_rename_ne_zero at hd
    obtain ⟨u, hud, hu⟩ := hd
    specialize h hu
    rw [← hud, ← h]
    exact symm_orderType σ u

lemma orderTypeComponent_symm {p : MvPolynomial α F} {a : Multiset ℕ} (σ : Perm α) :
  p ∈ orderTypeComponent α F a → σ • p ∈ orderTypeComponent α F a := by
    rw [mem_orderTypeComponent, mem_orderTypeComponent]
    exact stronglyHomogeneous_symm σ

lemma subset_orderTypeComponent {p : MvPolynomial α F} {a : Multiset ℕ} (hp : stronglyHomogeneous p a) :
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

lemma orderTypeComponent_subset_homoSub (a : Multiset ℕ) :
  ((orderTypeComponent α F a) : Set (MvPolynomial α F)) ⊆ ↑(homogeneousSubmodule α F a.sum) := by
    intro q
    simp only [SetLike.mem_coe, mem_orderTypeComponent, mem_homogeneousSubmodule]
    exact isHomogeneous_of_stronglyHomogeneous a

variable [DecidableEq α]

lemma minDeg_orderTypeComponent {a : Multiset ℕ} (h : ∃ p ∈ (orderTypeComponent α F a), p ≠ 0) :
  minDeg (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) = a.sum := by
    apply minDeg_homo h (orderTypeComponent_subset_homoSub a)

lemma homoSubI_orderTypeComponent (a : Multiset ℕ) :
  homogeneousSubmoduleI (minDeg (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))))
  (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) = orderTypeComponent α F a := by
    by_cases hp : ∃ p ∈ (orderTypeComponent α F a), p ≠ 0
    rw [minDeg_orderTypeComponent hp]
    rw [homoSubI_span a.sum ((orderTypeComponent α F a) : Set (MvPolynomial α F)) (orderTypeComponent_subset_homoSub a)]
    exact Submodule.span_eq (orderTypeComponent α F a)

    push_neg at hp
    apply (Submodule.eq_bot_iff _).mpr at hp
    rw [hp]
    simp only [Submodule.bot_coe, subset_refl, ideal_span_subset_zero_singleton,
      Submodule.zero_eq_bot, minDeg_bot]
    rw [← Submodule.zero_eq_bot, ← Submodule.zero_eq_bot, homoSubI_zero]

lemma singleDegGen_orderTypeComponent (a : Multiset ℕ) : IsSingleDegGen (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
  apply singleDegGen_iff.mpr
  use a.sum; use orderTypeComponent α F a; constructor
  exact orderTypeComponent_subset_homoSub a
  rfl

lemma stronglyHomogeneous_monomial_iff {a : Multiset ℕ} {d : α →₀ ℕ} {c : F} (hc : c ≠ 0) :
  stronglyHomogeneous (monomial d c) a ↔ orderType d = a := by
    simp only [stronglyHomogeneous, coeff_monomial, ne_eq, ite_eq_right_iff, hc, imp_false,
      Decidable.not_not, forall_eq']

open Classical
lemma monomials_span_orderTypeComponent {a : Multiset ℕ} :
  orderTypeComponent α F a = Submodule.span F ((fun d => (monomial d (1 : F)))
  '' {d : α →₀ ℕ | orderType d = a}) := by
    suffices orderTypeComponent α F a ≤ Submodule.span F ((fun d => (monomial d (1 : F)))
    '' {d : α →₀ ℕ | orderType d = a}) by
      apply antisymm this
      apply Submodule.span_le.mpr
      intro p; simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, mem_orderTypeComponent,
        forall_exists_index, and_imp]
      intro d hd hp
      rw [← hp]
      exact (stronglyHomogeneous_monomial_iff (one_ne_zero)).mpr hd
    intro p hp
    rw [mem_orderTypeComponent] at hp
    unfold stronglyHomogeneous at hp
    rw [as_sum p]
    apply Submodule.sum_mem
    intro d hd
    have hm : monomial d (1 : F) ∈ Submodule.span F ((fun d => (monomial d (1 : F)))
    '' {d : α →₀ ℕ | orderType d = a}) := by
      apply Submodule.subset_span
      simp only [Set.mem_image, Set.mem_setOf_eq, ne_eq, one_ne_zero, not_false_eq_true,
        monomial_left_inj, exists_eq_right]
      apply hp
      exact Finsupp.mem_support_iff.mp hd
    apply Submodule.smul_mem _ (coeff d p) at hm
    rw [smul_monomial, smul_eq_mul, mul_one] at hm
    exact hm



lemma permutation_of_orderType_eq' {n : ℕ} : ∀ d e : α →₀ ℕ, (orderType d).card = n →
  orderType d = orderType e → ∃ σ : Equiv.Perm α, Finsupp.mapDomain σ e = d := by
    induction n with
    | zero =>
    intro d e hc hde
    rw [Multiset.card_eq_zero, ← Multiset.empty_eq_zero] at hc
    rw [hc] at hde; symm at hde
    rw [orderType_empty_iff] at hc; rw [orderType_empty_iff] at hde
    rw [hc, hde];
    use 1; simp only [Perm.coe_one, Finsupp.mapDomain_zero]

    | succ n h =>
    intro d e hc hde

    let hc : 0 < (orderType e).card := by
      rw [hde] at hc
      exact Nat.lt_of_sub_eq_succ hc
    rw [Multiset.card_pos_iff_exists_mem] at hc
    obtain ⟨i, hi⟩ := hc
    rw [orderType, Multiset.mem_map] at hi
    obtain ⟨y, hy, hi⟩ := hi

    have hey : e y ∈ orderType e := by rw [orderType, Multiset.mem_map]; use y
    rw [← hde, orderType, Multiset.mem_map] at hey
    obtain ⟨x, hx, hxy⟩ := hey
    let d' : α →₀ ℕ := ⟨d.support \ {x}, fun z : α => if z = x then 0 else d z, by
      simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton, And.comm,
        ite_eq_left_iff, Classical.not_imp, implies_true]⟩
    let e' : α →₀ ℕ := ⟨e.support \ {y}, fun z : α => if z = y then 0 else e z, by
      simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton, And.comm,
        ite_eq_left_iff, Classical.not_imp, implies_true]⟩
    specialize h d' e' ?_ ?_
    simp [orderType, d']; simp [orderType] at hc
    rw [Multiset.card_erase_of_mem]
    simp [hc]
    exact hx

    simp [orderType, d', e']
    simp [orderType] at hde
    have hd1 : ∀ z ∈ (d.support.val.erase x), (fun z => if z = x then 0 else d z) z = d z := by
      intro z hz; apply Finset.ne_of_mem_erase at hz
      simp only [hz, ↓reduceIte]
    have he1 : ∀ z ∈ (e.support.val.erase y), (fun z => if z = y then 0 else e z) z = e z := by
      intro z hz; apply Finset.ne_of_mem_erase at hz
      simp only [hz, ↓reduceIte]

    rw [Multiset.map_congr rfl hd1, Multiset.map_congr rfl he1]
    rw [Multiset.map_erase_of_mem _ _ hx, Multiset.map_erase_of_mem _ _ hy]
    rw [hde, hxy]


    obtain ⟨τ, hτ⟩ := h
    have hτx : e' (Equiv.symm τ x) = 0 := by
      rw [Finsupp.ext_iff] at hτ; specialize hτ x
      rw [Finsupp.mapDomain_equiv_apply] at hτ
      rw [hτ, ← Finsupp.notMem_support_iff]
      simp [d']
    have hes : e.support = e'.support ∪ {y} := by
      simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union,
        Finset.singleton_subset_iff, e']
      exact hy
    let π : Equiv.Perm α := Equiv.swap y (Equiv.symm τ x)
    use (τ * π); ext z
    rw [Finsupp.mapDomain_equiv_apply]
    have hs : Equiv.symm (τ * π) = (Equiv.symm π)*(Equiv.symm τ) := by rfl
    rw [hs]; unfold π
    rw [Finsupp.ext_iff] at hτ; specialize hτ z
    rw [Finsupp.mapDomain_equiv_apply] at hτ
    unfold e' d' at hτ
    simp at hτ
    simp [Equiv.swap_apply_def]
    symm at hxy

    by_cases hzx : z = x
    simp [hzx]
    by_cases hsxy : Equiv.symm τ x = y
    simp [hsxy]; exact hxy
    simp [hsxy]; exact hxy

    simp [hzx]; simp [hzx] at hτ
    by_cases hzd : z ∈ d.support
    suffices (Equiv.symm τ) z ≠ y by simp [this]; simp [this] at hτ; exact hτ
    rw [Finsupp.mem_support_iff] at hzd
    contrapose! hzd; simp [hzd] at hτ
    symm; exact hτ

    rw [Finsupp.notMem_support_iff] at hzd
    rw [hzd]; simp [hzd] at hτ
    by_cases hzy : Equiv.symm τ z = y
    simp [hzy]
    rw [← Finsupp.notMem_support_iff, hes]
    simp; constructor; exact hτx
    rw [← hzy]; contrapose! hzx; symm
    apply_fun τ at hzx
    simp at hzx; exact hzx

    simp [hzy]; exact hτ hzy




lemma permutation_of_orderType_eq (d e : α →₀ ℕ) : orderType d = orderType e →
  ∃ σ : Equiv.Perm α, Finsupp.mapDomain σ e = d := by
    have hd : (orderType d).card = (orderType d).card := rfl
    exact permutation_of_orderType_eq' d e hd

lemma monomial_symmSpan_orderTypeComponent {d : α →₀ ℕ} :
  symmSpan {monomial d (1 : F)} = Ideal.span (orderTypeComponent α F (orderType d)) := by
    have hd : stronglyHomogeneous (monomial d (1 : F)) (orderType d) := by
      rw [stronglyHomogeneous_monomial_iff]; exact one_ne_zero
    apply antisymm (subset_orderTypeComponent hd)
    rw [Ideal.span, Submodule.span_le, monomials_span_orderTypeComponent, symmSpan,
      Ideal.span]
    suffices Submodule.span F ((fun d => (monomial d (1 : F))) '' {e : α →₀ ℕ | orderType e = orderType d}) ≤ Submodule.span F (symmSet {monomial d (1 : F)}) by
      apply subset_trans this
      apply Submodule.span_le_restrictScalars
    apply Submodule.span_mono
    intro m;
    simp only [Set.mem_image, Set.mem_setOf_eq, mem_symmSet_singleton,
      forall_exists_index, and_imp, symm_monomial]
    intro e hmsh hem
    rw [← hem]
    obtain ⟨σ, hσ⟩ := permutation_of_orderType_eq e d hmsh
    use σ; rw [hσ]


lemma exists_monomial_symmSpan_orderTypeComponent {a : Multiset ℕ}
  (h : ∃ p : MvPolynomial α F, p ≠ 0 ∧ stronglyHomogeneous p a) :
  ∃ d : α →₀ ℕ, Ideal.span (orderTypeComponent α F a) = symmSpan {monomial d (1 : F)} := by
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
    rw [stronglyHomogeneous_monomial_iff] at hd
    rw [← hd]; symm
    exact monomial_symmSpan_orderTypeComponent
    exact one_ne_zero

lemma psi_orderTypeComponent' {a : Multiset ℕ} :
  (∃ (p : MvPolynomial α F), p ≠ 0 ∧ stronglyHomogeneous p a) →
  IsPrincipalSymmetric (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
    intro h
    apply exists_monomial_symmSpan_orderTypeComponent at h
    obtain ⟨d, h⟩ := h
    use (monomial d (1 : F));

lemma psi_orderTypeComponent (a : Multiset ℕ) :
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

def orderTypes (p : MvPolynomial α F) := orderType '' {d : α →₀ ℕ | coeff d p ≠ 0}

lemma mem_orderTypes_iff_image_support {p : MvPolynomial α F} {a : Multiset ℕ} :
  a ∈ orderTypes p ↔ a ∈ (Finset.image orderType p.support).toSet := by
    simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq, Finset.coe_image, Finset.mem_coe,
      mem_support_iff]

lemma orderTypes_eq_image_support {p : MvPolynomial α F} : orderTypes p = (Finset.image orderType p.support).toSet := by
  ext a; exact mem_orderTypes_iff_image_support

lemma mem_orderTypes {p : MvPolynomial α F} {d : α →₀ ℕ} : coeff d p ≠ 0 → orderType d ∈ orderTypes p := by
  simp only [ne_eq, orderTypes, Set.mem_image, Set.mem_setOf_eq]
  intro h; use d

lemma orderTypes_singleton_iff_stronglyHomogeneous {p : MvPolynomial α F} {a : Multiset ℕ} (hpz : p ≠ 0) :
  stronglyHomogeneous p a ↔ orderTypes p = {a} := by
    constructor; intro h; unfold stronglyHomogeneous at h
    refine Set.eq_singleton_iff_unique_mem.mpr ?_
    constructor
    rw [ne_zero_iff] at hpz
    obtain ⟨d, hd⟩ := hpz
    specialize h hd; rw [← h]
    exact mem_orderTypes hd

    intro b hb
    simp [orderTypes] at hb
    obtain ⟨e, he, heb⟩ := hb
    apply h at he
    rw [← he, ← heb]


    intro h d hd
    apply mem_orderTypes at hd
    rw [h, Set.mem_singleton_iff] at hd
    exact hd

lemma orderTypes_monomial {d : α →₀ ℕ} : orderTypes (monomial d (1 : F)) = {orderType d} := by
  apply (orderTypes_singleton_iff_stronglyHomogeneous _).mp
  rw [stronglyHomogeneous_monomial_iff (one_ne_zero)]
  apply monomial_eq_zero.not.mpr one_ne_zero

lemma orderTypes_disjoint_iff {p q : MvPolynomial α F} : Disjoint (orderTypes p) (orderTypes q) ↔ ∀ d e : α →₀ ℕ,
  coeff d p ≠ 0 → coeff e q ≠ 0 → orderType d ≠ orderType e := by
    constructor; intro h d e hd he
    contrapose! h
    refine Set.not_disjoint_iff.mpr ?_
    use orderType d; constructor
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

lemma orderTypes_sum {X : Type*} {s : Finset X} {f : X → MvPolynomial α F}
  (h : ∀ x y, x ∈ s → y ∈ s → x ≠ y → Disjoint (orderTypes (f x)) (orderTypes (f y))) :
  orderTypes (∑ x ∈ s, f x) = ⋃ x ∈ s, orderTypes (f x) := by
    apply antisymm orderTypes_sum_subset
    intro a ha
    rw [Set.mem_iUnion₂] at ha
    obtain ⟨x, hxs, ha⟩ := ha

    have haot : ∀ y ∈ s, x ≠ y → a ∉ orderTypes (f y) := by
      intro y hys hxy
      specialize h x y hxs hys hxy
      exact Disjoint.notMem_of_mem_left h ha
    simp [orderTypes]
    simp [orderTypes] at ha
    obtain ⟨d, hdf, hda⟩ := ha
    use d; constructor; swap; exact hda
    contrapose! haot
    suffices ∃ y ∈ s, y ≠ x ∧ coeff d (f y) ≠ 0 by
      obtain ⟨y, hy0, hy1, hy2⟩ := this
      apply mem_orderTypes at hy2
      rw [hda] at hy2; symm at hy1
      use y
    contrapose! haot
    suffices coeff d (∑ x ∈ s, f x) = coeff d (f x) by rw [this]; exact hdf
    rw [coeff_sum]
    apply Finset.sum_eq_single_of_mem x hxs haot

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
  exact symm_orderType σ e

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
  use orderType d
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
