import Mathlib

variable {R : Type*} [Semiring R]

noncomputable
def min_gen_size (I : Ideal R) : ℕ
  := sInf { n : ℕ | ∃ S : Finset R, 0 ∉ S ∧ S.card = n ∧ I = Ideal.span ↑S}

variable {I : Ideal R}

@[simp] lemma mgs_bot : min_gen_size (⊥ : Ideal R) = 0 := by
  unfold min_gen_size
  suffices 0 ∈ {n | ∃ S : Finset R, 0 ∉ S ∧ S.card = n ∧ (0 : Ideal R) = Ideal.span S} by
    apply Nat.sInf_eq_zero.mpr; left; exact this
  rw [Set.mem_setOf]; use ∅
  constructor; exact Finset.notMem_empty 0; constructor
  rfl; symm
  simp only [Finset.coe_empty, Ideal.span_empty, Submodule.zero_eq_bot]

lemma mgs_pos [hnr : IsNoetherianRing R] (h : I ≠ ⊥) : min_gen_size I > 0 := by
  apply Nat.pos_iff_ne_zero.mpr
  unfold min_gen_size
  apply Nat.sInf_eq_zero.not.mpr
  simp only [Set.mem_setOf_eq, Finset.card_eq_zero, existsAndEq, Finset.notMem_empty,
    not_false_eq_true, Finset.coe_empty, Ideal.span_empty, true_and, not_or]
  constructor; exact h
  obtain ⟨S, hspan⟩ := ((isNoetherianRing_iff_ideal_fg R).mp hnr) I
  symm at hspan
  let S' := S.toSet \ {0}
  have hsf : Fintype S' := by exact Fintype.ofFinite ↑S'
  let S'' := S'.toFinset
  push_neg; use (S''.card); rw [Set.mem_setOf]
  use S''; constructor; simp only [Set.mem_toFinset, Set.mem_diff, Finset.mem_coe,
    Set.mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true, S'', S']
  constructor; rfl
  simp [S'', S']; rw [hspan]; symm
  apply Submodule.span_sdiff_singleton_zero

@[simp] lemma mgs_top [Nontrivial R] : min_gen_size (⊤ : Ideal R) = 1 := by
  have h1 : 1 ∈ {n : ℕ | ∃ S : Finset R, 0 ∉ S ∧ S.card  = n ∧ (⊤ : Ideal R) = Ideal.span ↑S} := by
    rw [Set.mem_setOf]
    use {1}; constructor; simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true]
    constructor; rfl
    simp only [Finset.coe_singleton, Ideal.span_singleton_one]
  apply antisymm (Nat.sInf_le h1)

  suffices 0 ∉ {n : ℕ | ∃ S : Finset R, 0 ∉ S ∧ S.card  = n ∧ (⊤ : Ideal R) = Ideal.span ↑S} by
    apply le_csInf
    use 1; intro n hn
    apply Nat.one_le_iff_ne_zero.mpr
    contrapose! this
    rw [this] at hn
    exact hn
  by_contra!
  rw [Set.mem_setOf] at this
  obtain ⟨S, hzS, hcard, hspan⟩ := this
  apply Finset.card_eq_zero.mp at hcard
  rw [hcard] at hspan
  simp only [Finset.coe_empty, Ideal.span_empty, top_ne_bot] at hspan
