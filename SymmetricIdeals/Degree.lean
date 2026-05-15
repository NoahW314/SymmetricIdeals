/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.MinDeg

open MvPolynomial

variable {α R : Type*} [CommSemiring R]

noncomputable def highestDegree (p : MvPolynomial α R) := sSup {i | homogeneousComponent i p ≠ 0}
noncomputable def lowestDegree (p : MvPolynomial α R) := sInf {i | homogeneousComponent i p ≠ 0}

@[simp]
lemma highestDegree_zero : highestDegree (0 : MvPolynomial α R) = 0 := by
  simp [highestDegree]

@[simp]
lemma lowestDegree_zero : lowestDegree (0 : MvPolynomial α R) = 0 := by
  simp [lowestDegree]

lemma bddAbove_setOf_homogeneousComponent {p : MvPolynomial α R} :
    BddAbove {i | homogeneousComponent i p ≠ 0} := by
  rw [bddAbove_def]
  use p.totalDegree
  intro i hi
  rw [Set.mem_setOf] at hi
  contrapose! hi
  exact homogeneousComponent_eq_zero i p hi

lemma nonempty_setOf_homogeneousComponent {p : MvPolynomial α R} (hp : p ≠ 0) :
    {i | homogeneousComponent i p ≠ 0}.Nonempty := by
  rw [← sum_homogeneousComponent p] at hp
  apply Finset.exists_ne_zero_of_sum_ne_zero at hp
  obtain ⟨i, hi, hp⟩ := hp
  use i
  rwa [Set.mem_setOf]

lemma lowestDegree_le_highestDegree (p : MvPolynomial α R) : lowestDegree p ≤ highestDegree p := by
  by_cases hp : p = 0
  · simp [hp]
  refine csInf_le_csSup (nonempty_setOf_homogeneousComponent hp) ?_
    bddAbove_setOf_homogeneousComponent
  rw [bddBelow_def]
  use 0
  simp

lemma homogeneousComponent_eq_zero_of_lt_lowestDegree {p : MvPolynomial α R} {i : ℕ}
    (h : i < lowestDegree p) : homogeneousComponent i p = 0 := by
  contrapose! h
  refine Nat.sInf_le ?_
  rwa [Set.mem_setOf]

lemma homogeneousComponent_highestDegree_ne_zero {p : MvPolynomial α R} (hp : p ≠ 0) :
    homogeneousComponent (highestDegree p) p ≠ 0 := by
  suffices highestDegree p ∈ {i | homogeneousComponent i p ≠ 0} by rwa [Set.mem_setOf] at this
  exact Nat.sSup_mem (nonempty_setOf_homogeneousComponent hp)
    bddAbove_setOf_homogeneousComponent

lemma lowestDegree_component_ne_zero {p : MvPolynomial α R} (hp : p ≠ 0) :
    homogeneousComponent (lowestDegree p) p ≠ 0 := by
  suffices lowestDegree p ∈ {i | homogeneousComponent i p ≠ 0} by rwa [Set.mem_setOf] at this
  exact Nat.sInf_mem (nonempty_setOf_homogeneousComponent hp)

lemma highestDegree_eq_totalDegree {p : MvPolynomial α R} : highestDegree p = p.totalDegree := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine le_antisymm ?_ ?_
  · by_contra! h
    exact homogeneousComponent_highestDegree_ne_zero hp0 (homogeneousComponent_eq_zero _ _ h)
  · simp only [totalDegree, highestDegree, ne_eq, Finset.sup_le_iff, mem_support_iff]
    intro d hd
    refine le_csSup bddAbove_setOf_homogeneousComponent ?_
    rw [Finsupp.sum, Set.mem_setOf_eq]
    contrapose! hd
    apply_fun (coeff d) at hd
    simpa [coeff_homogeneousComponent, Finsupp.degree] using hd

theorem highestDegree_mul [NoZeroDivisors R] {p q : MvPolynomial α R} (hp : p ≠ 0) (hq : q ≠ 0) :
    highestDegree (p * q) = highestDegree p + highestDegree q := by
  simp only [highestDegree_eq_totalDegree]
  exact totalDegree_mul_of_isDomain hp hq

lemma homogeneousComponent_lowestDegree_add_mul {p q : MvPolynomial α R} :
    homogeneousComponent (lowestDegree p + lowestDegree q) (p * q) =
    (homogeneousComponent (lowestDegree p) p) * (homogeneousComponent (lowestDegree q) q) := by
  rw [homogeneousComponent_mul, Finset.sum_eq_single_of_mem (lowestDegree p, lowestDegree q)]
  · rw [Finset.mem_antidiagonal]
  intro x hx hxl
  rw [Finset.mem_antidiagonal] at hx
  wlog! hxp : x.1 > lowestDegree p
  · rw [add_comm x.1, add_comm (lowestDegree p)] at hx
    specialize this (x.2, x.1) hx ?_ ?_
    · grind
    · grind
    · rwa [mul_comm]
  have hxq : x.2 < lowestDegree q := by grind
  rw [homogeneousComponent_eq_zero_of_lt_lowestDegree hxq, mul_zero]

theorem lowestDegree_mul [NoZeroDivisors R] {p q : MvPolynomial α R} (hp : p ≠ 0) (hq : q ≠ 0) :
    lowestDegree (p * q) = lowestDegree p + lowestDegree q := by
  refine le_antisymm ?_ ?_
  · refine Nat.sInf_le ?_
    rw [Set.mem_setOf, homogeneousComponent_lowestDegree_add_mul]
    exact mul_ne_zero (lowestDegree_component_ne_zero hp) (lowestDegree_component_ne_zero hq)
  · refine le_csInf (nonempty_setOf_homogeneousComponent (mul_ne_zero hp hq)) ?_
    intro i hi
    rw [Set.mem_setOf] at hi
    suffices ∃ j k, j + k = i ∧ lowestDegree p ≤ j ∧ lowestDegree q ≤ k by grind
    rw [homogeneousComponent_mul] at hi
    apply Finset.exists_ne_zero_of_sum_ne_zero at hi
    obtain ⟨x, hi, hx⟩ := hi
    rw [Finset.mem_antidiagonal] at hi
    rw [mul_ne_zero_iff] at hx
    use x.1, x.2
    constructor
    · exact hi
    constructor
    · exact Nat.sInf_le hx.1
    · exact Nat.sInf_le hx.2

theorem isHomogeneous_iff_lowestDegree_eq_highestDegree {p : MvPolynomial α R} :
    p.IsHomogeneous p.totalDegree ↔ highestDegree p = lowestDegree p := by
  by_cases! hp0 : p = 0
  · simp [hp0, isHomogeneous_zero]
  constructor
  · intro h
    unfold highestDegree lowestDegree
    suffices {i | homogeneousComponent i p ≠ 0} = {p.totalDegree} by simp [this]
    ext i
    simp [homogeneousComponent_of_mem h, hp0]
  · intro h
    suffices {i | homogeneousComponent i p ≠ 0} = {p.totalDegree} by
      suffices p = homogeneousComponent p.totalDegree p by
        nth_rw 1 [this]
        exact homogeneousComponent_isHomogeneous p.totalDegree p
      suffices ∀ i < p.totalDegree, homogeneousComponent i p = 0 by
        nth_rw 1 [← sum_homogeneousComponent p]
        rw [Finset.sum_eq_single_of_mem]
        · exact Finset.self_mem_range_succ p.totalDegree
        · grind
      intro i hi
      contrapose! hi
      refine le_of_eq ?_
      suffices i ∈ {p.totalDegree} by
        rw [Set.mem_singleton_iff] at this
        exact this.symm
      rwa [← this, Set.mem_setOf]
    ext i
    simp only [ne_eq, Set.mem_setOf_eq, ← highestDegree_eq_totalDegree, Set.mem_singleton_iff]
    constructor
    · intro hi
      refine le_antisymm (le_csSup bddAbove_setOf_homogeneousComponent hi) ?_
      rw [h, lowestDegree]
      exact Nat.sInf_le hi
    · intro hi
      rw [hi]
      exact homogeneousComponent_highestDegree_ne_zero hp0

lemma isHomogeneous_of_dvd_isHomogeneous [NoZeroDivisors R] {p q : MvPolynomial α R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) (h : q ∣ p) : q.IsHomogeneous q.totalDegree := by
  obtain ⟨r, hr⟩ := h
  have hq0 : q ≠ 0 := by lia
  have hr0 : r ≠ 0 := by lia
  rw [isHomogeneous_iff_lowestDegree_eq_highestDegree]
  rw [← IsHomogeneous.totalDegree hp hp0, isHomogeneous_iff_lowestDegree_eq_highestDegree, hr,
    highestDegree_mul hq0 hr0, lowestDegree_mul hq0 hr0] at hp
  have hq := lowestDegree_le_highestDegree q
  have hr := lowestDegree_le_highestDegree r
  lia
