/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Basic
import SymmetricIdeals.MinimalGenerating
import SymmetricIdeals.SingleDegGen

open MvPolynomial Equiv Rename

variable {α R : Type*} [CommSemiring R]


def orderType (d : α →₀ ℕ) := Multiset.map d d.support.val

@[simp]
lemma orderType_zero : orderType (0 : α →₀ ℕ) = ∅ := by
  simp [orderType]

lemma orderType_empty_iff {d : α →₀ ℕ} : orderType d = ∅ ↔ d = 0 := by
  simp [orderType]


namespace MvPolynomial

def IsStronglyHomogeneous (p : MvPolynomial α R) (a : Multiset ℕ) :=
  ∀ ⦃d⦄, coeff d p ≠ 0 → (orderType d) = a

end MvPolynomial

@[simp]
lemma isStronglyHomogeneous_constant (c : R) :
    IsStronglyHomogeneous (C c : MvPolynomial α R) ∅ := by
  classical simp only [IsStronglyHomogeneous, coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp,
    Multiset.empty_eq_zero, and_imp, forall_eq', orderType_zero, implies_true]

@[simp]
lemma isStronglyHomogeneous_one : IsStronglyHomogeneous (1 : MvPolynomial α R) 0 := by
  exact isStronglyHomogeneous_constant 1

lemma isStronglyHomogeneous_empty_iff {p : MvPolynomial α R} :
    IsStronglyHomogeneous p ∅ ↔ ∃ c : R, p = C c := by
  constructor
  · intro h
    simp_rw [IsStronglyHomogeneous, orderType_empty_iff] at h
    use coeff 0 p
    ext d
    classical rw [coeff_C]
    grind
  · intro h
    obtain ⟨c, h⟩ := h
    rw [h]
    exact isStronglyHomogeneous_constant c

lemma orderType_sum_eq_degree {d : α →₀ ℕ} : (orderType d).sum = d.degree := by
  simp [orderType, Finsupp.degree]

lemma isHomogeneous_of_isStronglyHomogeneous {p : MvPolynomial α R} (a : Multiset ℕ)
    (h : p.IsStronglyHomogeneous a) : p.IsHomogeneous (Multiset.sum a) := by
  intro d hd
  rw [← h hd, orderType_sum_eq_degree, Finsupp.degree_eq_weight_one]
  rfl

lemma isStronglyHomogeneous_add {p q : MvPolynomial α R} (a : Multiset ℕ)
    (hp : IsStronglyHomogeneous p a) (hq : IsStronglyHomogeneous q a) :
    IsStronglyHomogeneous (p + q) a := by
  simp_all only [IsStronglyHomogeneous, coeff_add]
  grind [zero_add]

@[simp]
lemma isStronglyHomogeneous_zero (a : Multiset ℕ) :
    IsStronglyHomogeneous (0 : MvPolynomial α R) a := by
  simp [IsStronglyHomogeneous]

lemma isStronglyHomogeneous_smul (a : Multiset ℕ) (c : R) {p : MvPolynomial α R}
    (h : IsStronglyHomogeneous p a) : IsStronglyHomogeneous (c • p) a := by
  simp only [IsStronglyHomogeneous, ne_eq, coeff_smul, smul_eq_mul] at ⊢ h
  intro d hd
  by_cases! hdp : coeff d p = 0
  · simp [hdp] at hd
  · exact h hdp

variable (α R) in
def orderTypeComponent (a : Multiset ℕ) : Submodule R (MvPolynomial α R) where
  carrier := {p : MvPolynomial α R | IsStronglyHomogeneous p a}
  add_mem' := isStronglyHomogeneous_add a
  zero_mem' := isStronglyHomogeneous_zero a
  smul_mem' := isStronglyHomogeneous_smul a

lemma mem_orderTypeComponent_iff {p : MvPolynomial α R} {a : Multiset ℕ} :
    p ∈ orderTypeComponent α R a ↔ IsStronglyHomogeneous p a := by
  simp [orderTypeComponent]

@[simp]
lemma orderType_mapDomain (σ : Perm α) (d : α →₀ ℕ) : orderType (Finsupp.mapDomain (⇑σ) d) =
    orderType d := by
  unfold orderType
  let i : (x : α) → x ∈ (Finsupp.mapDomain (⇑σ) d).support.val → α := fun x hx => (Equiv.symm σ) x
  refine Multiset.map_eq_map_of_bij_of_nodup ⇑(Finsupp.mapDomain (⇑σ) d)
      ⇑d (Finsupp.mapDomain (⇑σ) d).support.nodup d.support.nodup i ?_ ?_ ?_ ?_
  · simp [i]
  · simp [i]
  · simp only [Finset.mem_val, Finsupp.mem_support_iff, ne_eq, Finsupp.mapDomain_equiv_apply,
      exists_prop, i]
    intro x hx
    use σ x
    simp [hx]
  · simp [i]

lemma perm_isStronglyHomogeneous {p : MvPolynomial α R} {a : Multiset ℕ} (σ : Perm α)
    (h : p.IsStronglyHomogeneous a) : (σ • p).IsStronglyHomogeneous a := by
  simp only [IsStronglyHomogeneous, ne_eq, symmAct_def] at h ⊢
  intro d hd
  obtain ⟨u, hud, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  rw [← hud, ← h hu]
  exact orderType_mapDomain σ u

lemma perm_mem_orderTypeComponent_of_mem {p : MvPolynomial α R} {a : Multiset ℕ} (σ : Perm α)
    (h : p ∈ orderTypeComponent α R a) : σ • p ∈ orderTypeComponent α R a := by
  rw [mem_orderTypeComponent_iff] at h ⊢
  exact perm_isStronglyHomogeneous σ h

lemma isSymmetric_orderTypeComponent {a : Multiset ℕ} :
    Rename.IsSymmetric (SetLike.coe (orderTypeComponent α R a)) := by
  intro σ p hp
  exact perm_mem_orderTypeComponent_of_mem σ hp

lemma symmSpan_le_span_orderTypeComponent {p : MvPolynomial α R} {a : Multiset ℕ}
    (hp : p.IsStronglyHomogeneous a) :
    symmSpan {p} ≤ Ideal.span ((orderTypeComponent α R a)) := by
  rw [symmSpan_singleton_le_iff_mem (span_isSymmetric isSymmetric_orderTypeComponent)]
  refine Submodule.mem_span_of_mem ?_
  exact hp

lemma orderTypeComponent_le_homogeneousSubmodule (a : Multiset ℕ) :
    orderTypeComponent α R a ≤ homogeneousSubmodule α R a.sum := by
  intro p
  exact isHomogeneous_of_isStronglyHomogeneous a

lemma minDeg_orderTypeComponent {a : Multiset ℕ} (h : ∃ p ∈ (orderTypeComponent α R a), p ≠ 0) :
    minDeg (Ideal.span (SetLike.coe (orderTypeComponent α R a))) = a.sum :=
  minDeg_homog h (orderTypeComponent_le_homogeneousSubmodule a)

lemma homogSubI_orderTypeComponent (a : Multiset ℕ) :
    homogeneousSubmoduleI (minDeg (Ideal.span (SetLike.coe (orderTypeComponent α R a))))
    (Ideal.span (SetLike.coe (orderTypeComponent α R a))) = orderTypeComponent α R a := by
  by_cases! hp : ∃ p ∈ (orderTypeComponent α R a), p ≠ 0
  · rw [minDeg_orderTypeComponent hp, homogSubI_span a.sum (SetLike.coe (orderTypeComponent α R a))
      (orderTypeComponent_le_homogeneousSubmodule a), Submodule.span_eq (orderTypeComponent α R a)]
  · rw [← Submodule.eq_bot_iff] at hp
    simp [hp]

lemma isSingleDegGen_orderTypeComponent (a : Multiset ℕ) :
    IsSingleDegGen (Ideal.span (SetLike.coe (orderTypeComponent α R a))) := by
  rw [isSingleDegGen_iff]
  use a.sum, orderTypeComponent α R a
  constructor
  · exact orderTypeComponent_le_homogeneousSubmodule a
  rfl

lemma isStronglyHomogeneous_monomial_iff {a : Multiset ℕ} {d : α →₀ ℕ} {c : R} (hc : c ≠ 0) :
    IsStronglyHomogeneous (monomial d c) a ↔ orderType d = a := by
  classical simp [IsStronglyHomogeneous, hc]

lemma orderTypeComponent_eq_span {a : Multiset ℕ} : orderTypeComponent α R a =
    Submodule.span R ((fun d => (monomial d (1 : R))) '' {d : α →₀ ℕ | orderType d = a}) := by
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [mem_orderTypeComponent_iff] at hp
    rw [as_sum p]
    refine Submodule.sum_mem _ ?_
    intro d hd
    rw [← mul_one (coeff d p), ← smul_eq_mul, ← smul_monomial]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.mem_span_of_mem ?_
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use d
    constructor
    · rw [mem_support_iff] at hd
      exact hp hd
    · rfl
  · rw [Submodule.span_le]
    intro p
    simp only [Set.mem_image, Set.mem_setOf_eq, orderTypeComponent, Submodule.coe_set_mk,
      AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, forall_exists_index, and_imp]
    intro d hd hdp
    subst hdp
    by_cases! h0 : (1 : R) = 0
    · simp [h0]
    exact (isStronglyHomogeneous_monomial_iff h0).mpr hd


lemma permutation_of_orderType_eq' {n : ℕ} (d e : α →₀ ℕ) (hc : (orderType d).card = n)
    (hde : orderType d = orderType e) : ∃ σ : Equiv.Perm α, Finsupp.mapDomain σ e = d := by
  classical
  induction n generalizing d e
  · rw [Multiset.card_eq_zero, ← Multiset.empty_eq_zero] at hc
    rw [hc] at hde
    symm at hde
    rw [orderType_empty_iff] at hc hde
    rw [hc, hde]
    use 1
    simp
  · rename_i n h
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
    · simp [orderType] at hc
      simp [orderType, d', Multiset.card_erase_of_mem hx, hc]
    · simp only [orderType, Finset.sdiff_val, Finset.singleton_val, Multiset.sub_singleton,
        Finsupp.coe_mk, d', e'] at hde ⊢
      have hd1 : ∀ z ∈ (d.support.val.erase x), (fun z => if z = x then 0 else d z) z = d z := by
        grind [Multiset.Nodup.mem_erase_iff d.support.nodup]
      have he1 : ∀ z ∈ (e.support.val.erase y), (fun z => if z = y then 0 else e z) z = e z := by
        grind [Multiset.Nodup.mem_erase_iff e.support.nodup]
      rw [Multiset.map_congr rfl hd1, Multiset.map_congr rfl he1, Multiset.map_erase_of_mem _ _ hx,
        Multiset.map_erase_of_mem _ _ hy, hde, hxy]
    obtain ⟨τ, hτ⟩ := h
    have hτx : e' (Equiv.symm τ x) = 0 := by simp [← Finsupp.mapDomain_equiv_apply, hτ, d']
    have hes : e.support = e'.support ∪ {y} := by
      simpa only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union,
        Finset.singleton_subset_iff, e']
    let π : Equiv.Perm α := Equiv.swap y (Equiv.symm τ x)
    use τ * π
    ext z
    rw [Finsupp.mapDomain_equiv_apply]
    have hs : (τ * π).symm = π.symm * τ.symm := by
      rfl
    rw [hs]
    unfold π
    rw [Finsupp.ext_iff] at hτ
    specialize hτ z
    rw [Finsupp.mapDomain_equiv_apply] at hτ
    simp only [Finsupp.coe_mk, e', d'] at hτ
    simp only [symm_swap, Perm.coe_mul, Function.comp_apply, swap_apply_def,
      EmbeddingLike.apply_eq_iff_eq]
    symm at hxy
    by_cases! hzx : z = x
    · simp only [hzx, ↓reduceIte]
      by_cases hsxy : Equiv.symm τ x = y
      · simpa [hsxy]
      · simpa [hsxy]
    · simp only [hzx, ↓reduceIte] at hτ ⊢
      by_cases hzd : z ∈ d.support
      · suffices (Equiv.symm τ) z ≠ y by simpa [this] using hτ
        rw [Finsupp.mem_support_iff] at hzd
        contrapose! hzd
        symm
        simpa [hzd] using hτ
      · rw [Finsupp.notMem_support_iff] at hzd
        rw [hzd]
        by_cases hzy : Equiv.symm τ z = y
        · simp only [hzy, ↓reduceIte]
          rw [← Finsupp.notMem_support_iff, hes]
          simp only [Finset.union_singleton, Finset.mem_insert, Finsupp.mem_support_iff, ne_eq,
            not_or, Decidable.not_not]
          constructor
          · rw [← hzy]
            contrapose! hzx
            symm
            apply_fun τ at hzx
            simpa using hzx
          · exact hτx
        · simp [hzd] at hτ
          simp [hzy, hτ]




lemma permutation_of_orderType_eq (d e : α →₀ ℕ) : orderType d = orderType e →
  ∃ σ : Equiv.Perm α, Finsupp.mapDomain σ e = d := by
    have hd : (orderType d).card = (orderType d).card := rfl
    exact permutation_of_orderType_eq' d e hd

@[simp]
lemma orderTypeComponent_of_subsingleton [Subsingleton R] (a : Multiset ℕ) :
    orderTypeComponent α R a = ⊥ := by
  simp [Submodule.eq_bot_iff, orderTypeComponent, Subsingleton.eq_zero (α := MvPolynomial α R)]

lemma symmSpan_monomial_eq_span_orderTypeComponent {d : α →₀ ℕ} :
    symmSpan {monomial d (1 : R)} = Ideal.span (orderTypeComponent α R (orderType d)) := by
  by_cases! hR : Subsingleton R
  · simp [orderTypeComponent_of_subsingleton, hR.allEq 1 0]
  have hd : IsStronglyHomogeneous (monomial d (1 : R)) (orderType d) := by
    rw [isStronglyHomogeneous_monomial_iff one_ne_zero]
  refine le_antisymm (symmSpan_le_span_orderTypeComponent hd) ?_
  rw [Ideal.span_le, orderTypeComponent_eq_span]
  refine le_trans ?_ (Submodule.span_le_restrictScalars R (MvPolynomial α R) _)
  refine Submodule.span_mono ?_
  intro m
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_symmSet_singleton, perm_monomial,
    forall_exists_index, and_imp]
  intro e hmsh hem
  rw [← hem]
  obtain ⟨σ, hσ⟩ := permutation_of_orderType_eq e d hmsh
  use σ
  rw [hσ]


lemma exists_symmSpan_monomial_eq_span_orderTypeComponent {a : Multiset ℕ}
    {p : MvPolynomial α R} (hp0 : p ≠ 0) (hp : p.IsStronglyHomogeneous a) :
    ∃ d : α →₀ ℕ, symmSpan {monomial d (1 : R)} = Ideal.span (orderTypeComponent α R a) := by
  have h10 : (1 : R) ≠ 0 := by
    contrapose! hp0
    symm at hp0
    rw [subsingleton_iff_zero_eq_one] at hp0
    exact Subsingleton.eq_zero p
  rw [MvPolynomial.ne_zero_iff] at hp0
  obtain ⟨d, hpd⟩ := hp0
  have hd : IsStronglyHomogeneous (monomial d (1 : R)) a := by
    intro e he
    classical simp only [coeff_monomial, ne_eq, ite_eq_right_iff, Classical.not_imp] at he
    rw [← he.1]
    exact hp hpd
  use d
  rw [isStronglyHomogeneous_monomial_iff h10] at hd
  rw [← hd]
  exact symmSpan_monomial_eq_span_orderTypeComponent

lemma isPSI_span_orderTypeComponent (a : Multiset ℕ) :
    IsPrincipalSymmetric (Ideal.span (SetLike.coe (orderTypeComponent α R a))) := by
  by_cases h : orderTypeComponent α R a = ⊥
  · simp [h]
  simp only [Submodule.eq_bot_iff, not_forall] at h
  obtain ⟨p, hp, hp0⟩ := h
  obtain ⟨d, h⟩ := exists_symmSpan_monomial_eq_span_orderTypeComponent hp0 hp
  use (monomial d (1 : R))
  symm
  exact h

section DisjointOrderTypes

abbrev orderTypes (p : MvPolynomial α R) := Finset.image orderType p.support

@[simp]
lemma orderTypes_zero : orderTypes (0 : MvPolynomial α R) = ∅ := by
  simp

lemma mem_orderTypes_of_coeff_ne_zero {p : MvPolynomial α R} {d : α →₀ ℕ} (h : coeff d p ≠ 0) :
    orderType d ∈ orderTypes p := by
  simp only [orderTypes, Finset.mem_image, mem_support_iff, ne_eq]
  use d

lemma orderTypes_eq_empty_iff_eq_zero {p : MvPolynomial α R} : orderTypes p = ∅ ↔ p = 0 := by
  constructor
  · contrapose!
    intro h
    obtain ⟨d, h⟩ := exists_coeff_ne_zero h
    use orderType d
    exact mem_orderTypes_of_coeff_ne_zero h
  · simp

lemma orderTypes_singleton_iff_isStronglyHomogeneous {p : MvPolynomial α R} {a : Multiset ℕ}
    (hp0 : p ≠ 0) : orderTypes p = {a} ↔ p.IsStronglyHomogeneous a := by
  constructor
  · intro h d hd
    apply mem_orderTypes_of_coeff_ne_zero at hd
    simpa [h, Finset.mem_singleton] using hd
  · intro h
    unfold IsStronglyHomogeneous at h
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [ne_zero_iff] at hp0
      obtain ⟨d, hd⟩ := hp0
      specialize h hd
      rw [← h]
      exact mem_orderTypes_of_coeff_ne_zero hd
    · intro b hb
      simp only [orderTypes, Finset.mem_image, mem_support_iff, ne_eq] at hb
      obtain ⟨e, he, heb⟩ := hb
      rw [← h he, ← heb]

@[simp]
lemma orderTypes_monomial [Nontrivial R] {d : α →₀ ℕ} :
    orderTypes (monomial d (1 : R)) = {orderType d} := by
  simp [orderTypes_singleton_iff_isStronglyHomogeneous,
    isStronglyHomogeneous_monomial_iff one_ne_zero]

lemma orderTypes_disjoint_iff {p q : MvPolynomial α R} :
    Disjoint (orderTypes p) (orderTypes q) ↔
    ∀ d e : α →₀ ℕ, coeff d p ≠ 0 → coeff e q ≠ 0 → orderType d ≠ orderType e := by
  rw [Finset.disjoint_iff_ne]
  contrapose!
  constructor
  · intro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_image, mem_support_iff, ne_eq] at ha hb
    obtain ⟨d, hd, hda⟩ := ha
    obtain ⟨e, he, heb⟩ := hb
    rw [hab, ← heb] at hda
    use d, e
  · intro ⟨d, e, hd, he, hde⟩
    use orderType d
    constructor
    · exact mem_orderTypes_of_coeff_ne_zero hd
    · use orderType e
      constructor
      · exact mem_orderTypes_of_coeff_ne_zero he
      · exact hde

lemma orderTypes_add_subset {p q : MvPolynomial α R} :
    orderTypes (p + q) ⊆ orderTypes p ∪ orderTypes q := by
  intro s
  simp only [Finset.mem_image, mem_support_iff, coeff_add, ne_eq, Finset.mem_union,
    forall_exists_index, and_imp]
  intro d hdc hds
  by_cases! hdz : coeff d p ≠ 0
  · left
    use d
  · rw [hdz, zero_add] at hdc
    right
    use d

lemma orderTypes_sum_subset {X : Type*} {s : Finset X} {f : X → MvPolynomial α R} :
    orderTypes (∑ x ∈ s, f x) ⊆ s.biUnion (fun x ↦ orderTypes (f x)) := by
  intro a
  simp only [Finset.mem_image, mem_support_iff, ne_eq, Finset.mem_biUnion, forall_exists_index,
    and_imp]
  intro d hd hda
  rw [coeff_sum] at hd
  obtain ⟨x, hx, hdx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  use x
  constructor
  · exact hx
  · use d

lemma orderTypes_add {p q : MvPolynomial α R} (h : Disjoint (orderTypes p) (orderTypes q)) :
    orderTypes (p + q) = orderTypes p ∪ orderTypes q := by
  refine le_antisymm orderTypes_add_subset ?_
  intro s hs
  rw [Finset.mem_union] at hs
  wlog hsp : s ∈ orderTypes p
  · grind [add_comm]
  have hsq : s ∉ orderTypes q := Disjoint.notMem_of_mem_left_finset h hsp
  simp only [Finset.mem_image, mem_support_iff, ne_eq, coeff_add] at hsp ⊢
  obtain ⟨d, hdp, hds⟩ := hsp
  use d
  constructor
  · contrapose! hsq
    rw [← hds]
    refine mem_orderTypes_of_coeff_ne_zero ?_
    contrapose! hsq
    rw [hsq, add_zero]
    exact hdp
  · exact hds

lemma orderTypes_sum {X : Type*} {s : Finset X} {f : X → MvPolynomial α R}
    (h : ∀ x y, x ∈ s → y ∈ s → x ≠ y → Disjoint (orderTypes (f x)) (orderTypes (f y))) :
    orderTypes (∑ x ∈ s, f x) = s.biUnion (fun x ↦ orderTypes (f x)) := by
  classical
  by_cases! hs : s = ∅
  · simp [hs]
  obtain ⟨x, hx⟩ := hs
  have hs' : ∀ y z, y ∈ s.erase x → z ∈ s.erase x → y ≠ z →
    Disjoint (orderTypes (f y)) (orderTypes (f z)) := by grind
  rw [← Finset.add_sum_erase s _ hx, orderTypes_add, orderTypes_sum hs']
  · have hot : orderTypes (f x) ∪ (s.erase x).biUnion (fun y ↦ orderTypes (f y)) =
      (insert x (s.erase x)).biUnion (fun y ↦ orderTypes (f y)) := by rw [Finset.biUnion_insert]
    rw [hot, Finset.insert_erase hx]
  · rw [orderTypes_sum hs', Finset.disjoint_biUnion_right]
    grind
  termination_by s.card
  decreasing_by classical exact Finset.card_erase_lt_of_mem hx

lemma orderTypes_subset_of_add_eq_add {p₁ p₂ q₁ q₂ : MvPolynomial α R}
    (hp : Disjoint (orderTypes p₁) (orderTypes p₂))
    (hpq₁ : Disjoint (orderTypes p₁) (orderTypes q₁))
    (hpq₂ : Disjoint (orderTypes p₂) (orderTypes q₂)) (h : p₁ + q₁ = p₂ + q₂) :
    orderTypes p₁ ⊆ orderTypes q₂ := by
  rw [← Finset.coe_subset]
  rw [← Finset.disjoint_coe] at hp
  refine Disjoint.subset_right_of_subset_union ?_ hp
  rw [← Finset.coe_union, Finset.coe_subset]
  calc orderTypes p₁
    _ ⊆ orderTypes p₁ ∪ orderTypes q₁ := Finset.subset_union_left
    _ = orderTypes (p₁ + q₁) := (orderTypes_add hpq₁).symm
    _ = orderTypes (p₂ + q₂) := by rw [h]
    _ = orderTypes p₂ ∪ orderTypes q₂ := orderTypes_add hpq₂

@[simp]
lemma orderTypes_smul_of_ne_zero [IsDomain R] {p : MvPolynomial α R} {c : R} (h : c ≠ 0) :
    orderTypes (c • p) = orderTypes p := by
  simp [orderTypes, support_smul_eq h]

lemma orderTypes_smul {p : MvPolynomial α R} {c : R} : orderTypes (c • p) ⊆ orderTypes p := by
  refine Finset.image_mono _ ?_
  exact support_smul

lemma orderTypes_disjoint_add {p q₁ q₂ : MvPolynomial α R}
    (h1 : Disjoint (orderTypes p) (orderTypes q₁))
    (h2 : Disjoint (orderTypes p) (orderTypes q₂)) :
    Disjoint (orderTypes p) (orderTypes (q₁+q₂)) :=
  Disjoint.mono_right orderTypes_add_subset <| Finset.disjoint_union_right.mpr ⟨h1, h2⟩

private lemma aux_orderTypes_perm {p : MvPolynomial α R} {σ : Perm α} :
    orderTypes (σ • p) ⊆ orderTypes p := by
  intro s
  simp only [Finset.mem_image, mem_support_iff, ne_eq, forall_exists_index, and_imp]
  intro d hd hds
  obtain ⟨e, hed, he⟩ := coeff_rename_ne_zero _ _ _ hd
  use e
  constructor
  · exact he
  rw [← hds, ← hed, orderType_mapDomain]

@[simp]
lemma orderTypes_perm (p : MvPolynomial α R) (σ : Perm α) : orderTypes (σ • p) = orderTypes p := by
  refine le_antisymm aux_orderTypes_perm ?_
  nth_rw 1 [show p = σ.symm • (σ • p) by exact inv_smul_eq_iff.mp rfl]
  exact aux_orderTypes_perm

lemma orderTypes_eq_of_mem_symmSet {p q : MvPolynomial α R} (h : q ∈ symmSet {p}) :
    orderTypes q = orderTypes p := by
  obtain ⟨σ, h⟩ := mem_symmSet_singleton.mp h
  rw [← h, orderTypes_perm]

lemma eq_zero_of_disjoint_add {f p q : MvPolynomial α R} (hsum : f = p + q)
    (hpq : Disjoint (orderTypes f) (orderTypes q))
    (hpq' : Disjoint (orderTypes p) (orderTypes q)) :
    q = 0 := by
  rw [hsum] at hpq
  rw [← orderTypes_eq_empty_iff_eq_zero, ← Finset.subset_empty]
  refine hpq ?_ (by rfl)
  simp [orderTypes_add hpq']

lemma eq_zero_of_disjoint_sum {p : MvPolynomial α R} {r : ℕ} {q : Fin r → MvPolynomial α R}
    (hsum : p = ∑ i, q i)
    (hdot : ∀ i j : Fin r, i ≠ j → Disjoint (orderTypes (q i)) (orderTypes (q j)))
    (i₀ : Fin r) (hq : ∀ i : Fin r, i ≠ i₀ → Disjoint (orderTypes (q i)) (orderTypes p))
    (i : Fin r) (hi₀ : i ≠ i₀) : q i = 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
  refine eq_zero_of_disjoint_add hsum (disjoint_comm.mp (hq i hi₀)) ?_
  refine Disjoint.mono_left orderTypes_sum_subset ?_
  rw [Finset.disjoint_biUnion_left]
  grind


section CommRing

variable {R : Type*} [CommRing R]

lemma orderTypes_sub_subset {p q : MvPolynomial α R} (h : orderTypes p ⊆ orderTypes q) :
    orderTypes (q - p) ⊆ orderTypes q := by
  intro s hs
  simp only [Finset.mem_image, mem_support_iff, coeff_sub, ne_eq] at hs
  obtain ⟨d, hdpq, hs⟩ := hs
  by_cases hd : coeff d p = 0
  · simp only [Finset.mem_image, mem_support_iff, ne_eq]
    use d
    constructor
    · rw [hd, sub_zero] at hdpq
      exact hdpq
    · exact hs
  · apply mem_orderTypes_of_coeff_ne_zero at hd
    rw [hs] at hd
    exact h hd

lemma orderTypes_disjoint_sub {p q r : MvPolynomial α R}
    (hpq : Disjoint (orderTypes p) (orderTypes q)) (hqr : orderTypes r ⊆ orderTypes q) :
    Disjoint (orderTypes p) (orderTypes (q - r)) := by
  apply orderTypes_sub_subset at hqr
  exact Finset.disjoint_of_subset_right hqr hpq

@[simp]
lemma orderTypes_neg (p : MvPolynomial α R) : orderTypes (-p) = orderTypes p := by
  simp [orderTypes]

lemma disjoint_sub_orderTypes_of_add_eq_add {p₁ p₂ q₁ q₂ : MvPolynomial α R}
    (hp : Disjoint (orderTypes p₁) (orderTypes p₂))
    (hpq₁ : Disjoint (orderTypes p₁) (orderTypes q₁)) (h : p₁ + q₁ = p₂ + q₂) :
    Disjoint (orderTypes p₁) (orderTypes (q₂ - p₁)) := by
  rw [show q₂ - p₁ = q₁ + (-p₂) by grind]
  rw [← orderTypes_neg p₂] at hp
  exact orderTypes_disjoint_add hpq₁ hp

end CommRing


end DisjointOrderTypes
