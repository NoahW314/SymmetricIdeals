/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Symmetry.Basic
import SymmetricIdeals.Homogeneous.SingleDegGen

open MvPolynomial Rename Equiv

attribute [local instance] MvPolynomial.gradedAlgebra

variable {α R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial α R)}

theorem isSingleDegGen_symmSpan {p : MvPolynomial α R} {n : ℕ} (h : p.IsHomogeneous n) :
    IsSingleDegGen (symmSpan {p}) := by
  rw [isSingleDegGen_iff]
  use n, symmSet {p}
  simp [symmSet_subset_homogSub_of_isHomogeneous h]

lemma minDeg_symmSpan {f : MvPolynomial α R} {n : ℕ} (h : f.IsHomogeneous n) (h0 : f ≠ 0) :
    minDeg (symmSpan {f}) = n := by
  refine minDeg_homog ?_ ?_
  · use f
    simp only [mem_symmSet_singleton_self, ne_eq, h0, not_false_eq_true, and_self]
  · rw [← Set.le_iff_subset, symmSet_le_iff isSymmetric_homogeneousSubmodule]
    simp [h]

lemma lowestDegree_perm {f : MvPolynomial α R} {σ : Perm α} :
    lowestDegree (σ • f) = lowestDegree f := by
  simp [lowestDegree, ← symmAct_homogeneousComponent, smul_eq_zero_iff_eq]

lemma minDeg_gen_eq {f : MvPolynomial α R} (h : I = symmSpan {f})
    (hI : I.IsHomogeneous (homogeneousSubmodule α R)) : minDeg I = lowestDegree f := by
  by_cases! hf0 : f = 0
  · simp_all
  rw [span_union_homogeneousComponent_image h hI, ← Ideal.span_sdiff_singleton_zero, minDeg_homog']
  · have hf : lowestDegree f ∈
        lowestDegree '' ((⋃ n, homogeneousComponent n '' symmSet {f}) \ {0}) := by
      simp only [Set.mem_image, Set.mem_diff, Set.mem_iUnion, mem_symmSet_singleton,
        exists_exists_eq_and, Set.mem_singleton_iff, ne_eq, ↓existsAndEq, true_and]
      use lowestDegree f, 1
      simp only [one_smul, homogeneousComponent_lowestDegree_ne_zero hf0, not_false_eq_true,
        true_and]
      rw [lowestDegree_of_isHomogeneous (homogeneousComponent_isHomogeneous _ _)]
      exact homogeneousComponent_lowestDegree_ne_zero hf0
    refine le_antisymm (Nat.sInf_le hf) ?_
    refine le_csInf ?_ ?_
    · use lowestDegree f
    · simp only [Set.mem_image, Set.mem_diff, Set.mem_iUnion, mem_symmSet_singleton,
        exists_exists_eq_and, Set.mem_singleton_iff, ne_eq, ↓existsAndEq, true_and,
        forall_exists_index, and_imp]
      intro n m σ hhc hm
      subst hm
      rw [lowestDegree_of_isHomogeneous (homogeneousComponent_isHomogeneous _ _) hhc]
      apply lowestDegree_le_of_homogeneousComponent_ne_zero at hhc
      rwa [lowestDegree_perm] at hhc
  · simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_image, mem_symmSet_singleton,
      exists_exists_eq_and, Set.mem_singleton_iff, ne_eq, and_imp, forall_exists_index]
    intro g n σ hg hg0
    subst hg
    use n
    exact homogeneousComponent_isHomogeneous n (σ • f)
  · simp

lemma exists_homog_eq_symmSpan_of_isPSI (hI : IsSingleDegGen I) (h : IsPrincipalSymmetric I) :
    ∃ f, f.IsHomogeneous (minDeg I) ∧ I = symmSpan {f} := by
  have h' := h
  obtain ⟨f, h⟩ := h
  by_cases! hf0 : f = 0
  · use 0
    simp [hf0, h, isHomogeneous_zero]
  use homogeneousComponent (minDeg I) f
  constructor
  · exact homogeneousComponent_isHomogeneous _ _
  refine le_antisymm ?_ ?_
  · nth_rw 1 [hI, isSingleDegGen_symmSpan (homogeneousComponent_isHomogeneous _ f)]
    refine Ideal.span_mono ?_
    refine le_trans (homogComps_gen_singleDegGen_ideal hI h) ?_
    suffices minDeg I = minDeg (symmSpan {(homogeneousComponent (minDeg I)) f}) by
      refine le_of_eq ?_
      rw [← this]
      congr
      ext g
      simp [mem_symmSet_singleton]
    rw [minDeg_symmSpan (homogeneousComponent_isHomogeneous _ _ )]
    rw [minDeg_gen_eq h (isHomogeneous_of_isSingleDegGen hI)]
    exact homogeneousComponent_lowestDegree_ne_zero hf0
  · rw [symmSpan_singleton_le_iff_mem (isSymmetric_of_isPSI h')]
    refine homogeneousComponent_mem_of_mem (isHomogeneous_of_isSingleDegGen hI) ?_ _
    simp [h]

-- move
lemma exists_homog_gen_of_psi_isSingleDegGen (hI : IsSingleDegGen I) (h : IsPrincipalSymmetric I) :
    ∃ f, f.IsHomogeneous (minDeg I) ∧ I = symmSpan {f} := by
  have h' := h
  obtain ⟨f, h⟩ := h
  by_cases hb : I = ⊥
  · use 0
    simp [isHomogeneous_zero, hb]
  · apply minDeg_mem' at hb
    specialize hb (isHomogeneous_of_isSingleDegGen hI)
    rw [Set.mem_setOf] at hb
    use (homogeneousComponent (minDeg I) f)
    constructor
    · exact homogeneousComponent_isHomogeneous (minDeg I) f
    have hssI : symmSpan {homogeneousComponent (minDeg I) f} ≤ I := by
      rw [symmSpan_singleton_le_iff_mem (isSymmetric_of_isPSI h')]
      refine homogeneousComponent_mem_of_mem (isHomogeneous_of_isSingleDegGen hI) ?_ _
      simp [h]
    suffices homogeneousSubmoduleI (minDeg I) I =
        homogeneousSubmoduleI (minDeg I) (symmSpan {(homogeneousComponent (minDeg I)) f}) by
      apply eq_of_homogSubI_eq hI
        <| isSingleDegGen_symmSpan (homogeneousComponent_isHomogeneous (minDeg I) f)
      rw [this]
      congr 1
      have hfz : homogeneousComponent (minDeg I) f ≠ 0 := by
        contrapose! hb
        rw [this, hb, symmSpan_zero, ← Submodule.zero_eq_bot]
        simp [Submodule.zero_eq_bot]
      rw [symmSpan, minDeg_homog]
      · use homogeneousComponent (minDeg I) f
        simp only [mem_symmSet_singleton_self, ne_eq, hfz, not_false_eq_true, and_true]
      · exact symmSet_subset_homogSub_of_isHomogeneous
          (homogeneousComponent_isHomogeneous (minDeg I) f)
    suffices homogeneousSubmoduleI (minDeg I) I ≥ homogeneousSubmoduleI (minDeg I)
        (symmSpan {(homogeneousComponent (minDeg I)) f}) by
      apply antisymm this
      suffices ⇑(homogeneousComponent (minDeg I)) '' symmSet {f} =
          symmSet {(homogeneousComponent (minDeg I)) f} by
        rw [symmSpan, ← this]
        exact homogComps_gen_singleDegGen_ideal hI h
      ext p
      simp only [Set.mem_image, mem_symmSet_singleton, exists_exists_eq_and,
        symmAct_homogeneousComponent]
    apply homogSubI_monotone (minDeg I) hssI
