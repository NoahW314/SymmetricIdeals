/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import SymmetricIdeals.Homogeneous.MinDeg
import SymmetricIdeals.Homogeneous.SingleDegGen
import SymmetricIdeals.Homogeneous.MinimalGenerators
import SymmetricIdeals.Upstream


open MvPolynomial

variable {α R : Type*} [Field R] {I : Ideal (MvPolynomial α R)} [Finite α]

attribute [local instance] MvPolynomial.gradedAlgebra

section Ring

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal (MvPolynomial α R)}

lemma homogSubI_mod_fin (n : ℕ) (I : Ideal (MvPolynomial α R)) :
    Module.Finite R (homogeneousSubmoduleI n I) := by
  rw [Module.Finite.iff_fg]
  exact Submodule.FG.of_le (homogeneousSubmodule_fg n) inf_le_left

lemma homogSubI_mod_fin' (n : ℕ) (I : Ideal (MvPolynomial α R)) :
    Module.Finite R (Submodule.span R ((homogeneousSubmoduleI n I) : Set (MvPolynomial α R))) := by
  rw [Submodule.span_eq]
  exact homogSubI_mod_fin n I

omit [Finite α] [IsNoetherianRing R] in
lemma finrank_hom_top [IsDomain R] : Module.finrank R (homogeneousSubmoduleI (minDeg
    (⊤ : Ideal (MvPolynomial α R))) (⊤ : Ideal (MvPolynomial α R))) = 1 := by
  rw [minDeg_top, ← Ideal.span_singleton_one, homogSubI_span]
  · rw [_root_.finrank_eq_one ⟨1, by simp⟩]
    · simp
    · simp [Submodule.mem_span_singleton]
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule,
      isHomogeneous_one α R]

end Ring


lemma finrank_mem_minDeg (h : IsSingleDegGen I) :
    ∃ S : Finset (MvPolynomial α R), (0 ∉ S ∧ I = Ideal.span S) ∧
    S.card = Module.finrank R (homogeneousSubmoduleI (minDeg I) I) := by
  have := homogSubI_mod_fin' (minDeg I) I
  obtain ⟨S, hsub, hcard, hspan, hlid⟩ := Submodule.exists_finset_span_eq_linearIndepOn R
    (SetLike.coe (homogeneousSubmoduleI (minDeg I) I))
  rw [Submodule.span_eq] at hspan hcard
  use S
  constructor
  constructor
  · apply LinearIndepOn.zero_notMem_image at hlid
    simpa using hlid
  · rw [h, ← hspan, Ideal.span, Submodule.span_span_of_tower]
  · rw [hcard]

theorem mgs_le_finrank (h : IsSingleDegGen I) : minGenSize I ≤
    Module.finrank R (homogeneousSubmoduleI (minDeg I) I) := by
  refine Nat.sInf_le ?_
  simp only [Set.mem_image, Set.mem_setOf]
  exact finrank_mem_minDeg h

theorem mgs_ge_finrank (h : IsSingleDegGen I) : minGenSize I ≥
    Module.finrank R (homogeneousSubmoduleI (minDeg I) I) := by
  classical
  have hmgs : minGenSize I ∈ Finset.card ''
      {S : Finset (MvPolynomial α R) | 0 ∉ S ∧ I = Ideal.span (SetLike.coe S)} := by
    refine Nat.sInf_mem ?_
    use Module.finrank R (homogeneousSubmoduleI (minDeg I) I)
    exact finrank_mem_minDeg h
  simp only [Set.mem_image, Set.mem_setOf_eq] at hmgs
  obtain ⟨S, ⟨hsz, hspan⟩, hcard⟩ := hmgs
  rw [← hcard, ge_iff_le]
  let S' := Finset.image (homogeneousComponent (minDeg I)) S
  have hhcS : ∀ p : S', ∃ q : S, (homogeneousComponent (minDeg I)) q = p.1 := by
      intro ⟨p, hp⟩
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      use ⟨q, hq⟩
  trans S'.card
  · suffices Module.finrank R (homogeneousSubmoduleI (minDeg I) I) ≤ Module.finrank R
        (Submodule.span R (SetLike.coe S')) by
      refine le_trans this ?_
      nth_rw 4 [← Finset.toFinset_coe S']
      exact finrank_span_le_card _
    refine Submodule.finrank_mono ?_
    rw [← homogSubI_span (minDeg I)]
    · exact homogComps_gen_singleDegGen_ideal_finset h hspan
    · intro p hp
      simp only [Finset.coe_image, Set.mem_image, SetLike.mem_coe, S'] at hp
      obtain ⟨x, hx, hp⟩ := hp
      rw [← hp, SetLike.mem_coe, mem_homogeneousSubmodule]
      exact homogeneousComponent_isHomogeneous _ _
  · exact Finset.card_image_le


theorem mgs_eq_finrank (h : IsSingleDegGen I) : minGenSize I =
    Module.finrank R (homogeneousSubmoduleI (minDeg I) I) :=
  antisymm (mgs_le_finrank h) (mgs_ge_finrank h)

lemma mgs_le_mgs {I J : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
    (h : minDeg I = minDeg J) (hIJ : I ≤ J) : minGenSize I ≤ minGenSize J := by
  rw [mgs_eq_finrank hI, mgs_eq_finrank hJ]
  have := homogSubI_mod_fin (minDeg J) J
  refine Submodule.finrank_mono ?_
  rw [h]
  exact homogSubI_monotone _ hIJ

lemma mgs_lt_mgs {I J : Ideal (MvPolynomial α R)} (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
    (h : minDeg I = minDeg J) (hIJ : I < J) : minGenSize I < minGenSize J := by
  rw [mgs_eq_finrank hI, mgs_eq_finrank hJ]
  have := homogSubI_mod_fin (minDeg J) J
  refine Submodule.finrank_lt_finrank_of_lt ?_
  rw [← h]
  exact homogSubI_strictMono (minDeg I) h rfl hI hJ hIJ
