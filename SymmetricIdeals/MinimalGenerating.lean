/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib

variable {R : Type*} [Semiring R]

noncomputable
def minGenSize (I : Ideal R) : ℕ :=
  sInf (Finset.card '' { S : Finset R | 0 ∉ S ∧ I = Ideal.span ↑S})

variable {I : Ideal R}

@[simp]
lemma mgs_bot : minGenSize (⊥ : Ideal R) = 0 := by
  simp [minGenSize, Nat.sInf_eq_zero]

lemma mgs_pos [hnr : IsNoetherianRing R] (h : I ≠ ⊥) : minGenSize I > 0 := by
  simp only [minGenSize, gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq, Nat.sInf_eq_zero, Set.mem_image,
    Set.mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.notMem_empty, not_false_eq_true,
    Finset.coe_empty, Submodule.span_empty, h, and_false, ← Set.not_nonempty_iff_eq_empty,
    Set.image_nonempty, false_or, not_not]
  obtain ⟨S, hspan⟩ := ((isNoetherianRing_iff_ideal_fg R).mp hnr) I
  classical use S \ {0}
  simp [hspan]

@[simp]
lemma mgs_top [Nontrivial R] : minGenSize (⊤ : Ideal R) = 1 := by
  unfold minGenSize
  refine antisymm (Nat.sInf_le ?_) ?_
  · simp only [Set.mem_image, Set.mem_setOf_eq]
    use {1}
    simp
  · simp only [Nat.one_le_iff_ne_zero, ne_eq, Nat.sInf_eq_zero, Set.mem_image, Set.mem_setOf_eq,
      Finset.card_eq_zero, exists_eq_right, Finset.notMem_empty, not_false_eq_true,
      Finset.coe_empty, Submodule.span_empty, top_ne_bot, and_false,
      ← Set.not_nonempty_iff_eq_empty, Set.image_nonempty, false_or, not_not]
    use {1}
    simp
