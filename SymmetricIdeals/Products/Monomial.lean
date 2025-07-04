import Mathlib
import SymmetricIdeals.Products.kSymmetric
import SymmetricIdeals.PsiObstructions
import SymmetricIdeals.MonomialPsi

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

open MvPolynomial

lemma degree_perm {d : α →₀ ℕ} (σ : Equiv.Perm α) : d.degree = (Finsupp.mapDomain σ d).degree := by
  unfold Finsupp.degree
  apply Finset.sum_equiv σ
  simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply,
    implies_true]
  simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply,
    implies_true]

lemma top_of_ne_bot_of_isEmpty {I : Ideal (MvPolynomial α F)} [IsEmpty α] (h : I ≠ ⊥) : I = ⊤ := by
  rw [Submodule.ne_bot_iff] at h
  obtain ⟨p, hpI, hpz⟩ := h
  rw [eq_C_of_isEmpty p] at hpI; rw [eq_C_of_isEmpty p] at hpz
  apply Ideal.eq_top_of_isUnit_mem I hpI
  rw [isUnit_map_iff, isUnit_iff_ne_zero]
  rw [ne_eq, map_eq_zero] at hpz
  exact hpz

lemma bddAbove_finsupp_range {d : α →₀ ℕ} : BddAbove (Set.range d) := by
  refine Set.Finite.bddAbove ?_
  suffices Set.range d ≤ (Multiset.map d d.support.val).toFinset.toSet ∪ {0} by
    apply Set.Finite.subset ?_ this
    simp only [Set.union_singleton, Finset.finite_toSet, Set.Finite.insert]
  intro n h
  rw [Set.mem_range] at h
  obtain ⟨x, h⟩ := h
  simp only [Set.union_singleton, Set.mem_insert_iff, Finset.mem_coe, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val, Finsupp.mem_support_iff, ne_eq]
  by_cases hn : n = 0
  left; exact hn
  right; use x; constructor; rw [h]; exact hn; exact h

lemma sSup_ne_zero_of_finsupp {d : α →₀ ℕ} (h : d ≠ 0) : sSup (Set.range d) ≠ 0 := by
  have h : ∃ x : α, d x ≠ 0 := by contrapose! h; exact Finsupp.ext h
  obtain ⟨x, h⟩ := h
  refine Nat.pos_iff_ne_zero.mp ?_
  rw [lt_csSup_iff bddAbove_finsupp_range]
  use (d x); constructor; rw [Set.mem_range]; use x
  apply Nat.pos_iff_ne_zero.mpr h
  use (d x); rw [Set.mem_range]; use x

lemma range_subset_of_perm {d : α →₀ ℕ} (σ : Equiv.Perm α) : Set.range d ⊆ Set.range (Finsupp.mapDomain σ d) := by
  intro n
  simp only [Set.mem_range, Finsupp.mapDomain_equiv_apply, forall_exists_index]
  intro x h
  use (σ x); rw [Equiv.symm_apply_apply]; exact h

lemma range_eq_of_perm {d : α →₀ ℕ} (σ : Equiv.Perm α) : Set.range d = Set.range (Finsupp.mapDomain σ d) := by
  apply antisymm (range_subset_of_perm σ)
  apply subset_trans (range_subset_of_perm σ⁻¹)
  rw [← Finsupp.mapDomain_comp, ← Equiv.Perm.coe_mul]
  simp only [inv_mul_cancel, Equiv.Perm.coe_one, Finsupp.mapDomain_id, subset_refl]



variable [DecidableEq α]



lemma monomial_kSymmetric_iff {d : α →₀ ℕ} : kSymmetric (monomial d (1 : F)) ↔
  ∃ n, ∀ x : α, d x = n := by
    constructor; intro h
    by_cases hα : Nonempty α
    obtain ⟨y⟩ := hα
    use d y
    intro x
    specialize h (Equiv.swap x y)
    obtain ⟨c, h⟩ := h
    rw [symm_monomial, smul_eq_C_mul, C_mul_monomial, mul_one] at h
    rw [monomial_eq_monomial_iff] at h
    simp only [one_ne_zero, false_and, or_false] at h
    apply And.left at h
    have h : (Finsupp.mapDomain (Equiv.swap x y) d) x = d x := by
      exact congrFun (congrArg DFunLike.coe h) x
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h
    symm; exact h

    simp only [not_nonempty_iff] at hα; use 0
    simp only [IsEmpty.forall_iff]


    intro h; obtain ⟨n, h⟩ := h
    intro σ; use 1; simp [symm_monomial]
    ext x; rw [h x, Finsupp.mapDomain_equiv_apply, h (Equiv.symm σ x)]

lemma monomial_homogeneous {d : α →₀ ℕ} : (monomial d (1 : F)).IsHomogeneous (d.degree) := by
  apply isHomogeneous_of_stronglyHomogeneous (orderType d)
  apply (stronglyHomogeneous_monomial_iff ?_).mpr
  rfl; exact one_ne_zero

lemma minDeg_mul_eq_add_minDeg {I J : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
  (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) : minDeg (I*J) = minDeg I + minDeg J := by
    rw [singleDegGen_iff'] at hI; rw [singleDegGen_iff'] at hJ
    obtain ⟨S, hI⟩ := hI; obtain ⟨T, hJ⟩ := hJ
    let hIJ := homoSpan_mul hI hJ
    rw [hIJ.2]
    apply minDeg_homo ?_ hIJ.1
    apply And.right at hIJ
    have hIJB : I*J ≠ ⊥ := by apply mul_ne_zero hIB hJB
    rw [hIJ] at hIJB
    contrapose! hIJB
    exact Ideal.span_eq_bot.mpr hIJB


theorem monomialProduct_Psi {I J : Ideal (MvPolynomial α F)} (hIm : ∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : F)) '' S))
  (hJm : ∃ T : Set (α →₀ ℕ), J = Ideal.span ((fun d => monomial d (1 : F)) '' T)) (hI : IsPrincipalSymmetric I)
  (hJ : IsPrincipalSymmetric J) (hIs : IsSingleDegGen I) (hJs : IsSingleDegGen J)
  (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) :
  IsPrincipalSymmetric (I*J) ↔ ∃ d : α →₀ ℕ, kSymmetric (monomial d (1 : F)) ∧ (I = symmSpan {monomial d 1} ∨ J = symmSpan {monomial d 1}) := by
    constructor; swap; intro h
    obtain ⟨d, hd, h⟩ := h
    wlog h' : I = symmSpan {monomial d 1}
    rw [Or.comm] at h; rw [mul_comm]
    apply this hJm hIm hJ hI hJs hIs hJB hIB d hd h
    simp only [h', or_false] at h
    exact h

    obtain ⟨p, hp⟩ := hJ
    rw [h', hp, productPsi_of_kSymmetric hd]
    use ((monomial d 1) * p)


    by_cases hα : ¬Nonempty α
    simp at hα; intro h
    use 0; constructor
    rw [monomial_kSymmetric_iff]; use 0; simp only [Finsupp.coe_zero, Pi.zero_apply, implies_true]
    left; simp only [monomial_zero', C_1, symmSpan_one]
    exact top_of_ne_bot_of_isEmpty hIB

    push_neg at hα
    contrapose!; intro h
    obtain ⟨a, haI⟩ := (monomial_iff_symmSpan_monomial hI hIs hIB).mp hIm
    obtain ⟨b, hbJ⟩ := (monomial_iff_symmSpan_monomial hJ hJs hJB).mp hJm
    have ha : ¬kSymmetric (monomial a (1: F)) := by
      specialize h a; contrapose! h
      simp only [h, haI, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_self]
    have hb : ¬kSymmetric (monomial b (1 : F)) := by
      specialize h b; contrapose! h
      simp only [h, ne_eq, hbJ, implies_true, and_self]
    let n := sSup (Set.range a); let m := sSup (Set.range b)
    rw [monomial_kSymmetric_iff.not] at ha; push_neg at ha
    rw [monomial_kSymmetric_iff.not] at hb; push_neg at hb
    have hafz : a ≠ 0 := by
      contrapose! ha; use 0; rw [ha]
      simp only [Finsupp.coe_zero, Pi.zero_apply, implies_true]
    have hbfz : b ≠ 0 := by
      contrapose! hb; use 0; rw [hb]
      simp only [Finsupp.coe_zero, Pi.zero_apply, implies_true]
    have hn : ∃ x, a x = n := by
      rw [← Set.mem_range]
      apply Nat.sSup_mem ?_ bddAbove_finsupp_range
      apply Set.range_nonempty_iff_nonempty.mpr hα
    have hm : ∃ y, b y = m := by
      rw [← Set.mem_range]
      apply Nat.sSup_mem ?_ bddAbove_finsupp_range
      apply Set.range_nonempty_iff_nonempty.mpr hα
    specialize ha n; specialize hb m
    obtain ⟨x, hn⟩ := hn; obtain ⟨i, ha⟩ := ha
    obtain ⟨y, hm⟩ := hm; obtain ⟨j, hb⟩ := hb

    have hax0 : a x ≠ 0 := by
      rw [hn]; exact sSup_ne_zero_of_finsupp hafz
    have haxp : a x > 0 := by exact Nat.zero_lt_of_ne_zero hax0
    have hby0 : b y ≠ 0 := by
      rw [hm]; exact sSup_ne_zero_of_finsupp hbfz

    have hxi : x ≠ i := by contrapose! ha; rw [← ha]; exact hn
    have hix : i ≠ x := by symm at hxi; exact hxi
    have hyj : y ≠ j := by contrapose! hb; rw [← hb]; exact hm
    have hjy : j ≠ y := by symm at hyj; exact hyj
    have hσ : ∃ σ : Equiv.Perm α, (Finsupp.mapDomain σ b) x = b y ∧ (Finsupp.mapDomain σ b) i = b j := by
      by_cases hyi : y = i
      have hyx : y ≠ x := by rw [hyi]; exact hix
      use (Equiv.swap x y) * (Equiv.swap x j)
      rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
      have hess : Equiv.symm (Equiv.swap x y * Equiv.swap x j) = Equiv.symm (Equiv.swap x j) * Equiv.symm (Equiv.swap x y) := by rfl
      simp only [hess, Equiv.symm_swap, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.swap_apply_left, ← hyi, Equiv.swap_apply_right, and_true]
      rw [Equiv.swap_apply_of_ne_of_ne hyx hyj]

      push_neg at hyi; let hiy := hyi; symm at hiy
      use (Equiv.swap x y) * (Equiv.swap i j)
      rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
      have hess : Equiv.symm (Equiv.swap x y * Equiv.swap i j) = Equiv.symm (Equiv.swap i j) * Equiv.symm (Equiv.swap x y) := by rfl
      simp only [hess, Equiv.symm_swap, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne hyi hyj, Equiv.swap_apply_of_ne_of_ne hix hiy]
      rw [Equiv.swap_apply_left]
      simp only [and_self]

    obtain ⟨σ, hσx, hσi⟩ := hσ
    let c := Finsupp.mapDomain σ b

    have hmdp : minDeg (I*J) = (a+c).degree := by
      rw [minDeg_mul_eq_add_minDeg hIs hJs hIB hJB, Finsupp.degree_add, haI, hbJ]
      rw [minDeg_symmSpan (monomial_homogeneous), minDeg_symmSpan (monomial_homogeneous)]
      rw [← degree_perm σ]
      rw [ne_eq, monomial_eq_zero.not]; exact one_ne_zero
      rw [ne_eq, monomial_eq_zero.not]; exact one_ne_zero
    have hmdp2 : minDeg (I*J) = (a+Finsupp.mapDomain (Equiv.swap x i) c).degree := by
      rw [hmdp, Finsupp.degree_add, Finsupp.degree_add, Nat.add_left_cancel_iff]
      exact degree_perm (Equiv.swap x i)

    apply not_psi_of_nonzero_disjoint_orderTypes (singleDegGen_mul hIs hJs) ?_ ?_
      (eval_one_monomial_one_ne_zero (a + c))
      (eval_one_monomial_one_ne_zero (a + (Finsupp.mapDomain (Equiv.swap x i) c)))
    rw [orderTypes_monomial, orderTypes_monomial, Set.disjoint_singleton]

    apply_fun (Multiset.count ((a+c) x))
    unfold orderType; symm
    rw [Multiset.count_map, Multiset.count_map]
    apply ne_of_lt
    apply Multiset.card_lt_card
    apply lt_of_le_of_ne

    have hnodup : (a+(Finsupp.mapDomain (Equiv.swap x i) c)).support.val.Nodup := by
      exact (a + Finsupp.mapDomain (⇑(Equiv.swap x i)) c).support.nodup
    apply Multiset.Nodup.filter (fun z => (a+c) x = (a + Finsupp.mapDomain (⇑(Equiv.swap x i)) c) z) at hnodup
    rw [Multiset.le_iff_subset hnodup]
    intro z
    simp
    intro haz hac; constructor
    intro haz0; rw [haz0, zero_add] at hac
    have hc2 : c x ≥ c ((Equiv.swap x i) z) := by
      rw [hσx, hm]; unfold m; rw [range_eq_of_perm σ]
      apply le_csSup
      rw [← range_eq_of_perm σ]; exact bddAbove_finsupp_range
      unfold c; simp only [Set.mem_range, exists_apply_eq_apply]
    apply Nat.add_lt_add_of_lt_of_le haxp at hc2
    rw [zero_add] at hc2
    apply ne_of_lt at hc2; symm at hc2
    contradiction

    rw [hac]
    refine Nat.add_left_cancel_iff.mpr ?_
    have hzx : z ≠ x := by
      contrapose! hac; rw [hac]
      rw [Equiv.swap_apply_left, ne_eq, Nat.add_left_cancel_iff]
      rw [hσx, hσi, hm]; push_neg; symm; exact hb
    have hzi : z ≠ i := by
      contrapose! hac; rw [hac]
      rw [Equiv.swap_apply_right, ne_eq, Nat.add_right_cancel_iff]
      rw [hn]; push_neg; symm; exact ha
    rw [Equiv.swap_apply_def]
    simp only [hzx, ↓reduceIte, hzi]


    apply (Multiset.Nodup.ext ?_ ?_).not.mpr; push_neg
    use x; right;
    simp
    constructor; intro hax
    rw [hσx, hσi, hm]; push_neg; symm; exact hb
    intro hax; rw [hσx]; exact hby0


    apply Multiset.Nodup.filter
    exact (a + Finsupp.mapDomain (⇑(Equiv.swap x i)) c).support.nodup
    apply Multiset.Nodup.filter
    exact (a + c).support.nodup


    rw [← mul_one 1, ← monomial_mul, haI, hbJ]
    refine Submodule.mul_mem_mul ?_ ?_
    exact mem_symmSpan_self
    exact mem_symmSpan_monomial σ

    rw [← mul_one 1, ← monomial_mul, haI, hbJ]
    refine Submodule.mul_mem_mul ?_ ?_
    exact mem_symmSpan_self
    unfold c; rw [← Finsupp.mapDomain_comp]
    apply mem_symmSpan_monomial ((Equiv.swap x i) * σ)

    rw [hmdp]; exact monomial_homogeneous
    rw [hmdp2]; exact monomial_homogeneous
