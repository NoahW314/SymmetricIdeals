/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib

lemma range_subset_range_mapDomain {α β M : Type*} [AddCommMonoid M] {f : α → β} (v : α →₀ M)
    (h : Function.Injective f) : Set.range v ⊆ Set.range (Finsupp.mapDomain f v) := by
  grind [Finsupp.mapDomain_apply]

lemma range_mapDomain_of_equiv {α β M : Type*} [AddCommMonoid M] (f : α ≃ β) (v : α →₀ M) :
    Set.range (Finsupp.mapDomain f v) = Set.range v := by
  grind [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_apply]


lemma Ideal.map_eq_image_of_surjective {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    (f : F) [RingHomClass F R S] (hf : Function.Surjective ⇑f) {I : Ideal R} :
    Ideal.map f I = ⇑f '' ↑I := by
  grind [Ideal.mem_map_iff_of_surjective f hf, SetLike.mem_coe]
