/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Homogeneous.Basic
import SymmetricIdeals.Upstream

open MvPolynomial

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable
def minDeg (I : Ideal (MvPolynomial α R)) := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}

@[simp]
lemma minDeg_bot : minDeg (⊥ : Ideal (MvPolynomial α R)) = 0 := by
  simp [minDeg]

@[simp]
lemma minDeg_top : minDeg (⊤ : Ideal (MvPolynomial α R)) = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp [Submodule.eq_bot_of_subsingleton]
  · simp [minDeg, ← Submodule.zero_eq_bot]

lemma minDeg_mem (h : minDeg I ≠ 0) : minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  refine Nat.sInf_mem ?_
  contrapose! h
  simp [minDeg, h]

lemma bot_of_empty_minDeg (h : I.IsHomogeneous (homogeneousSubmodule α R))
    (hIB : {n | homogeneousSubmoduleI n I ≠ ⊥} = ∅) : I = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [← sum_homogeneousComponent p]
  refine Finset.sum_eq_zero ?_
  intro i _
  contrapose! hIB
  use i
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq]
  use homogeneousComponent i p
  simp [hIB, homogeneousComponent_isHomogeneous, homogeneousComponent_mem_of_mem h hp]

lemma minDeg_mem' (h : I ≠ ⊥) (hI : I.IsHomogeneous (homogeneousSubmodule α R)) :
    minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  refine Nat.sInf_mem ?_
  contrapose! h
  exact bot_of_empty_minDeg hI h

lemma nonzero_homog_of_ne_bot (h : I ≠ ⊥) (hI : I.IsHomogeneous (homogeneousSubmodule α R)) :
    ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  obtain ⟨p, h⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <| minDeg_mem' h hI
  simp at h
  use p
  tauto

lemma nonzero_homog_of_minDeg_nonzero (h : minDeg I ≠ 0) :
    ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  obtain ⟨p, h⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <| minDeg_mem h
  simp at h
  use p
  tauto

theorem minDeg_antitone {J : Ideal (MvPolynomial α R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule α R)) (hb : I ≠ ⊥) (hIJ : I ≤ J) :
    minDeg I ≥ minDeg J := by
  refine Nat.sInf_le ?_
  simp only [ne_eq, ← bot_lt_iff_ne_bot, Set.mem_setOf_eq]
  refine lt_of_lt_of_le ?_ (homogSubI_monotone _ hIJ)
  rw [bot_lt_iff_ne_bot]
  exact minDeg_mem' hb hI

@[simp]
theorem minDeg_homog {n : ℕ} {S : Set (MvPolynomial α R)} (hS : ∃ p ∈ S, p ≠ 0)
    (h : S ⊆ homogeneousSubmodule α R n) : minDeg (Ideal.span S) = n := by
  have hn : n ∈ {n | homogeneousSubmoduleI n (Ideal.span S) ≠ ⊥} := by
    simp [homogSubI_span n S h, Submodule.span_eq_bot, hS]
  refine le_antisymm (Nat.sInf_le hn) ?_
  refine le_csInf (by use n) ?_
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq, forall_exists_index]
  intro m p hp hpS hp0
  by_contra! hnm
  rw [Submodule.mem_span_iff_exists_finset_subset] at hpS
  obtain ⟨f, T, hTS, hfT, hps⟩ := hpS
  suffices ∀ i ∈ Finset.range (p.totalDegree + 1), (homogeneousComponent i p) = 0 by
    rw [← sum_homogeneousComponent p] at hp0
    apply Finset.sum_eq_zero at this
    contradiction
  intro i hi
  rw [IsHomogeneous.totalDegree hp hp0, Finset.mem_range] at hi
  apply Nat.lt_of_lt_of_le hi at hnm
  simp only [← hps, smul_eq_mul, map_sum]
  refine Finset.sum_eq_zero ?_
  intro x hxT
  rw [homogeneousComponent_mul]
  refine Finset.sum_eq_zero ?_
  intro a ha
  refine mul_eq_zero_of_right _ ?_
  apply hTS at hxT
  apply h at hxT
  simp [homogeneousComponent_of_mem hxT]
  grind [Finset.mem_antidiagonal]

lemma minDeg_homogeneousSubmodule [Nonempty α]
    {R : Type*} [CommRing R] [Nontrivial R] [IsReduced R] {n : ℕ} :
    minDeg (Ideal.span (SetLike.coe (homogeneousSubmodule α R n))) = n := by
  refine minDeg_homog ?_ (by rfl)
  inhabit α
  use (X default) ^ n
  simp [isHomogeneous_X_pow default n]

section Field

variable {R : Type*} [Field R] {I : Ideal (MvPolynomial α R)}

lemma top_of_zero_mem_minDeg (h : 0 ∈ {n | homogeneousSubmoduleI n I ≠ ⊥}) : I = ⊤ := by
  simp only [ne_eq, Submodule.eq_bot_iff, Submodule.mem_inf, mem_homogeneousSubmodule,
    Submodule.restrictScalars_mem, and_imp, not_forall, Set.mem_setOf_eq] at h
  obtain ⟨p, hph, hp, hp0⟩ := h
  refine Ideal.eq_top_of_isUnit_mem _ hp ?_
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hph
  rw [hph, C_eq_zero] at hp0
  rw [hph]
  exact IsUnit.map C <| Ne.isUnit hp0

lemma minDeg_zero_iff (h : I.IsHomogeneous (homogeneousSubmodule α R)) :
    minDeg I = 0 ↔ I = ⊤ ∨ I = ⊥ := by
  constructor
  · rw [minDeg, Nat.sInf_eq_zero]
    intro hI
    rcases hI with hIT | hIB
    · left; exact top_of_zero_mem_minDeg hIT
    · right; exact bot_of_empty_minDeg h hIB
  · grind [minDeg_top, minDeg_bot]

lemma zero_of_minDeg_zero (hh : I.IsHomogeneous (homogeneousSubmodule α R)) (hIT : I ≠ ⊤)
    (h : minDeg I = 0) : I = 0 := by
  rw [Submodule.zero_eq_bot]
  rw [minDeg_zero_iff hh] at h
  tauto

end Field
