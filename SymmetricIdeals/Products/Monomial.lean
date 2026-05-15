/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Products.kSymmetric
import SymmetricIdeals.PsiObstructions
import SymmetricIdeals.MonomialPsi
import SymmetricIdeals.Upstream

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

open MvPolynomial Rename Equiv
open scoped Pointwise


-- this is being added to Mathlib
lemma degree_mapDomain {d : α →₀ ℕ} (σ : Perm α) : (Finsupp.mapDomain σ d).degree = d.degree := by
  simp [Finsupp.mapDomain, Finsupp.sum]
  dsimp [Finsupp.degree_apply]

lemma Nat.sSup_range_ne_zero {d : α →₀ ℕ} (h : d ≠ 0) : sSup (Set.range d) ≠ 0 := by
  have h : ∃ x : α, d x ≠ 0 := by contrapose! h; exact Finsupp.ext h
  obtain ⟨x, h⟩ := h
  refine Nat.pos_iff_ne_zero.mp ?_
  rw [lt_csSup_iff (Finsupp.finite_range _).bddAbove]
  · use d x
    simp [Nat.pos_iff_ne_zero, h]
  · rw [Set.range_nonempty_iff_nonempty]
    use x

lemma eq_top_of_ne_bot [IsEmpty α] (h : I ≠ ⊥)
    (hm : ∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : R)) '' S)) : I = ⊤ := by
  obtain ⟨S, hm⟩ := hm
  subst hm
  rcases Set.eq_empty_or_singleton_of_subsingleton S with hS | hS
  · simp [hS] at h
  · obtain ⟨a, hS⟩ := hS
    have ha : a = 0 := Subsingleton.allEq a 0
    subst ha
    simp [hS]

lemma exists_mapDomain (b : α →₀ ℕ) {x y i j : α} (hxi : x ≠ i) (hyj : y ≠ j) :
    ∃ σ : Perm α, (Finsupp.mapDomain σ b) x = b y ∧ (Finsupp.mapDomain σ b) i = b j := by
  classical
  by_cases! hyi : y = i
  · have hyx : y ≠ x := by
      rw [hyi]
      exact hxi.symm
    use (swap x y) * (swap x j)
    rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
    simp only [show (swap x y * swap x j).symm = (swap x j).symm * (swap x y).symm by rfl,
      symm_swap, Perm.coe_mul, Function.comp_apply, swap_apply_left, ← hyi, swap_apply_right,
      and_true, swap_apply_of_ne_of_ne hyx hyj]
  · use (swap x y) * (swap i j)
    rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
    simp [show (swap x y * swap i j).symm = (swap i j).symm * (swap x y).symm by rfl,
      symm_swap, Perm.coe_mul, Function.comp_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hyi hyj, swap_apply_of_ne_of_ne hxi.symm hyi.symm, swap_apply_left]

theorem monomialProduct_Psi {R : Type*} [CommRing R] [NoZeroDivisors R]
    {I J : Ideal (MvPolynomial α R)}
    (hIm : ∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : R)) '' S))
    (hJm : ∃ T : Set (α →₀ ℕ), J = Ideal.span ((fun d => monomial d (1 : R)) '' T))
    (hI : IsPrincipalSymmetric I) (hJ : IsPrincipalSymmetric J)
    (hIs : IsSingleDegGen I) (hJs : IsSingleDegGen J) (hIB : I ≠ ⊥) (hJB : J ≠ ⊥) :
    IsPrincipalSymmetric (I * J) ↔ ∃ d : α →₀ ℕ, kSymmetric (monomial d (1 : R)) ∧
    (I = symmSpan {monomial d 1} ∨ J = symmSpan {monomial d 1}) := by
  classical
  constructor
  swap
  · intro ⟨d, hd, h⟩
    wlog h' : I = symmSpan {monomial d 1}
    · rw [Or.comm] at h
      rw [mul_comm]
      apply this hJm hIm hJ hI hJs hIs hJB hIB d hd h
      simpa [h', or_false] using h
    obtain ⟨p, hp⟩ := hJ
    rw [h', hp, mul_symmSpan_of_kSymmetric hd]
    use ((monomial d 1) * p)
  by_cases! hR : Subsingleton R
  · intro _
    use 0
    have : Subsingleton (Ideal (MvPolynomial α R)) := by
      exact (Submodule.subsingleton_iff (MvPolynomial α R)).mpr (by infer_instance)
    simp [Subsingleton.allEq I ⊤]
  by_cases! hα : IsEmpty α
  · intro h
    use 0
    simp [eq_top_of_ne_bot hIB hIm]
  contrapose!
  intro h
  obtain ⟨a, haI⟩ := (monomial_iff_symmSpan_monomial hI hIs hIB).mp hIm
  obtain ⟨b, hbJ⟩ := (monomial_iff_symmSpan_monomial hJ hJs hJB).mp hJm
  have ha : ¬kSymmetric (monomial a (1 : R)) := by simpa [haI] using h a
  have hb : ¬kSymmetric (monomial b (1 : R)) := by simpa [hbJ] using h b
  let n := sSup (Set.range a)
  let m := sSup (Set.range b)
  rw [kSymmetric_monomial_iff.not] at ha hb
  push Not at ha hb
  have ha0 : a ≠ 0 := by
    contrapose! ha
    simp [ha]
  have hb0 : b ≠ 0 := by
    contrapose! hb
    simp [hb]
  have hn : ∃ x, a x = n := by
    rw [← Set.mem_range]
    exact Nat.sSup_mem (Set.range_nonempty_iff_nonempty.mpr hα) (Finsupp.finite_range _).bddAbove
  have hm : ∃ y, b y = m := by
    rw [← Set.mem_range]
    exact Nat.sSup_mem (Set.range_nonempty_iff_nonempty.mpr hα) (Finsupp.finite_range _).bddAbove
  specialize ha n
  specialize hb m
  obtain ⟨x, hn⟩ := hn
  obtain ⟨i, ha⟩ := ha
  obtain ⟨y, hm⟩ := hm
  obtain ⟨j, hb⟩ := hb
  have hax0 : a x ≠ 0 := by
    rw [hn]
    exact Nat.sSup_range_ne_zero ha0
  have hby0 : b y ≠ 0 := by
    rw [hm]
    exact Nat.sSup_range_ne_zero hb0
  have hxi : x ≠ i := by
    contrapose! ha
    rwa [← ha]
  have hyj : y ≠ j := by
    contrapose! hb
    rwa [← hb]
  obtain ⟨σ, hσx, hσi⟩ := exists_mapDomain b hxi hyj
  let c := Finsupp.mapDomain σ b
  have hmdp : minDeg (I * J) = (a + c).degree := by
    rw [minDeg_mul_eq_add_minDeg hIs hJs hIB hJB, map_add, haI, hbJ,
      minDeg_symmSpan (isHomogeneous_monomial _ rfl) (by simp),
      minDeg_symmSpan (isHomogeneous_monomial _ rfl) (by simp), degree_mapDomain σ]
  have hmdp2 : minDeg (I * J) = (a + Finsupp.mapDomain (swap x i) c).degree := by
    rw [hmdp, map_add, map_add, Nat.add_left_cancel_iff, degree_mapDomain (swap x i)]
  apply not_psi_of_nonzero_disjoint_orderTypes (isSingleDegGen_mul hIs hJs) ?_ ?_
    (evalOne_monomial_ne_zero (a + c))
    (evalOne_monomial_ne_zero (a + (Finsupp.mapDomain (swap x i) c)))
  · rw [orderTypes_monomial, orderTypes_monomial, Finset.disjoint_singleton]
    apply_fun (Multiset.count ((a + c) x))
    rw [orderType, orderType, Multiset.count_map, Multiset.count_map]
    symm
    refine ne_of_lt <| Multiset.card_lt_card <| lt_of_le_of_ne ?_ ?_
    · have hnodup : (a + (Finsupp.mapDomain (swap x i) c)).support.val.Nodup := by
        exact (a + Finsupp.mapDomain (⇑(swap x i)) c).support.nodup
      apply Multiset.Nodup.filter (fun z ↦ (a + c) x = (a + Finsupp.mapDomain (⇑(swap x i)) c) z)
        at hnodup
      rw [Multiset.le_iff_subset hnodup]
      intro z
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.mapDomain_equiv_apply, symm_swap,
        Multiset.mem_filter, Finset.mem_val, Finsupp.mem_support_iff, ne_eq, Nat.add_eq_zero_iff,
        not_and, and_imp]
      intro haz hac
      constructor
      · intro haz0
        rw [haz0, zero_add] at hac
        have hc2 : c x ≥ c ((swap x i) z) := by
          rw [hσx, hm]
          unfold m
          rw [← range_mapDomain_of_equiv σ]
          refine le_csSup ?_ ?_
          · rw [← range_mapDomain_of_equiv σ]
            exact (Finsupp.finite_range _).bddAbove
          · simp only [c, Set.mem_range, exists_apply_eq_apply]
        apply Nat.add_lt_add_of_lt_of_le (Nat.zero_lt_of_ne_zero hax0) at hc2
        simp [zero_add, hac] at hc2
      · rw [hac, Nat.add_left_cancel_iff.mpr]
        have hzx : z ≠ x := by
          contrapose! hac
          rw [hac, Equiv.swap_apply_left, ne_eq, Nat.add_left_cancel_iff, hσx, hσi, hm]
          exact hb.symm
        have hzi : z ≠ i := by
          contrapose! hac
          rw [hac, Equiv.swap_apply_right, ne_eq, Nat.add_right_cancel_iff, hn];
          exact ha.symm
        simp [swap_apply_def, hzx, hzi]
    apply (Multiset.Nodup.ext ?_ ?_).not.mpr
    · push Not
      use x
      right
      simp
      constructor
      · simp [c, hσx, hσi, hm, hb.symm]
      · simp [c, hσx, hby0]
    · exact Multiset.Nodup.filter _ (a + Finsupp.mapDomain (⇑(swap x i)) c).support.nodup
    · exact Multiset.Nodup.filter _ (a + c).support.nodup
  · rw [← mul_one 1, ← monomial_mul, haI, hbJ]
    exact Submodule.mul_mem_mul mem_symmSpan_self <| mem_symmSpan_monomial σ
  · rw [← mul_one 1, ← monomial_mul, haI, hbJ]
    refine Submodule.mul_mem_mul mem_symmSpan_self ?_
    simp only [← Finsupp.mapDomain_comp, c]
    apply mem_symmSpan_monomial ((swap x i) * σ)
  · rw [hmdp]; exact isHomogeneous_monomial _ rfl
  · rw [hmdp2]; exact isHomogeneous_monomial _ rfl
