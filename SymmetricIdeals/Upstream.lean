/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib

/-!
Lemmas to upstream to Mathlib.
-/

public section

@[simp]
theorem Finsupp.range_equivMapDomain {α β M : Type*} [Zero M] (f : α ≃ β) (l : α →₀ M) :
    Set.range (Finsupp.equivMapDomain f l) = Set.range l :=
  f.symm.surjective.range_comp l

@[simp]
theorem Finsupp.range_mapDomain_of_equiv {α β M : Type*} [AddCommMonoid M] {v : α →₀ M}
    (f : α ≃ β) : Set.range (Finsupp.mapDomain f v) = Set.range v := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain, range_equivMapDomain]
