import Mathlib
import SymmetricIdeals.GradedMinimalGenerators
import SymmetricIdeals.Basic
import SymmetricIdeals.OrderType

open MvPolynomial

variable {F : Type*} [Field F]
variable {α : Type*}


open Classical
lemma psi_mgs_factorial [Finite α] {I : Ideal (MvPolynomial α F)} : IsPrincipalSymmetric I →
  (min_gen_size I ≤ (Nat.card α).factorial) := by
    intro h; obtain ⟨f, h⟩ := h
    by_cases hfz : f = 0
    rw [hfz, symmSpan_zero] at h
    rw [h, mgs_bot]
    exact Nat.zero_le (Nat.card α).factorial

    let S' := symmSet {f}
    let F : MvPolynomial α F → Equiv.Perm α := fun g => if hg : ∃ σ : Equiv.Perm α, g = σ • f then Classical.choose hg else 1
    have hsi : Set.InjOn F S' := by
      intro g hg g' hg' hgg
      simp only [S', Set.mem_setOf, symmSet, Set.mem_iUnion, Set.image_singleton,
        Set.mem_singleton_iff] at hg
      simp only [S', Set.mem_setOf, symmSet, Set.mem_iUnion, Set.image_singleton,
        Set.mem_singleton_iff] at hg'
      simp only [hg, ↓reduceDIte, hg', F, S'] at hgg
      let hgc := Classical.choose_spec hg
      let hgc' := Classical.choose_spec hg'
      rw [hgc, hgc', hgg]
    have hfs' : S'.Finite := by
      apply Set.Finite.of_finite_image ?_ hsi
      exact Set.toFinite (F '' S')
    have hfs := hfs'.fintype
    let S := S'.toFinset
    let n := S.card

    have han : n ≤ (Nat.card α).factorial := by
      unfold n
      rw [← Nat.card_perm, ← Nat.card_eq_card_toFinset S']
      apply Set.InjOn.injective at hsi
      apply Finite.card_le_of_injective (S'.restrict F) hsi
    apply le_trans ?_ han
    apply Nat.sInf_le
    rw [Set.mem_setOf]
    use S; constructor
    rw [Set.mem_toFinset]
    exact zero_notMem_nonzero_symmSet hfz
    constructor; rfl
    rw [h]; unfold symmSpan; congr
    simp only [Set.coe_toFinset, S, S']


def eval_one : MvPolynomial α F →+* F := eval (fun _ => (1 : F))

lemma eval_one_monomial (d : α →₀ ℕ) (f : F) : eval_one (monomial d f) = f := by
  simp only [eval_one, eval, coe_eval₂Hom, eval₂_monomial, RingHom.id_apply, Finsupp.prod, one_pow,
    Finset.prod_const_one, mul_one]

lemma eval_one_monomial_one_ne_zero (d : α →₀ ℕ) : eval_one (monomial d (1 : F)) ≠ 0 := by
  rw [eval_one_monomial]; exact one_ne_zero

lemma eval_one_zero_invariant {S : Set (MvPolynomial α F)} (h : ∀ p ∈ S, eval_one p = 0) {p : MvPolynomial α F} :
  p ∈ symmSpan S → eval_one p = 0 := by
    intro hp
    unfold symmSpan symmSet at hp
    rw [Ideal.mem_span] at hp
    specialize hp (RingHom.ker eval_one) ?_; swap
    exact hp
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_image] at hq
    simp only [eval_one, SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨σ, r, hrS, hq⟩ := hq
    rw [← hq]
    simp [HSMul.hSMul, SMul.smul]
    rw [eval_rename, ← h r hrS, eval_one]
    congr

lemma eval_one_zero_invariant' {S : Set (MvPolynomial α F)} (h : ∀ p ∈ S, eval_one p = 0) {p : MvPolynomial α F} :
  eval_one p ≠ 0 → p ∉ symmSpan S := by
    contrapose!; exact eval_one_zero_invariant h

variable [DecidableEq α]

theorem strict_subset_orderType {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n} (hp : stronglyHomogeneous p a)
  (hpz : p ≠ 0) : eval_one p = 0 → symmSpan {p} < Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F)) := by
    intro h1; apply lt_of_le_of_ne
    exact subset_homoOrderType hp

    rw [ne_zero_iff] at hpz
    obtain ⟨d, hdz⟩ := hpz
    suffices monomial d (1 : F) ∈ Ideal.span (orderTypeComponent α F a) ∧ monomial d (1 : F) ∉ symmSpan {p} by
      obtain ⟨hmi, hms⟩ := this
      contrapose! hms
      rw [hms]; exact hmi
    constructor
    apply Ideal.subset_span
    simp only [orderTypeComponent, stronglyHomogeneous, ne_eq, Submodule.coe_set_mk,
      AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_setOf_eq]
    intro e he
    rw [coeff_monomial] at he
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at he
    rw [← he]
    exact hp hdz
    apply eval_one_zero_invariant'
    intro q hq; rw [Set.mem_singleton_iff] at hq
    rw [hq]; exact h1
    exact eval_one_monomial_one_ne_zero d

lemma minDeg_symmSpan {n : ℕ} {p : MvPolynomial α F} (h : p.IsHomogeneous n) (hpz : p ≠ 0) : minDeg (symmSpan {p}) = n := by
  apply minDeg_homo; use p; constructor
  rw [mem_symmSet_singleton]; use 1
  apply one_smul; exact hpz
  exact symmSet_homo_singleton h

lemma minDeg_stronglyHomogeneous_symmSpan {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n}
  (hp : stronglyHomogeneous p a) (hpz : p ≠ 0) : minDeg (symmSpan {p}) = minDeg (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) := by
    rw [minDeg_symmSpan (isHomogeneous_of_stronglyHomogeneous a hp) hpz, minDeg_orderTypeComponent]
    use p; constructor
    rw [mem_orderTypeComponent]
    exact hp; exact hpz


lemma mgs_le_orderTypeComponent_rank [Finite α] {n : ℕ} {p : MvPolynomial α F} {a : Nat.Partition n}
  (hp : stronglyHomogeneous p a) (hpz : p ≠ 0) : eval_one p = 0 →
  min_gen_size (symmSpan {p}) ≤ Module.finrank F (orderTypeComponent α F a) - 1 := by
    intro h1
    rw [← homoSubI_orderTypeComponent a, ← mgs_eq_rank (singleDegGen_orderTypeComponent a)]
    suffices min_gen_size (symmSpan {p}) < min_gen_size (Ideal.span ((orderTypeComponent α F a) : Set (MvPolynomial α F))) by
      exact Nat.le_sub_one_of_lt this
    apply mgs_lt_mgs
    exact singleDegGen_of_symmSpan (isHomogeneous_of_stronglyHomogeneous a hp)
    exact singleDegGen_orderTypeComponent a
    exact minDeg_stronglyHomogeneous_symmSpan hp hpz
    exact strict_subset_orderType hp hpz h1


variable {I : Ideal (MvPolynomial α F)}

lemma all_fin_of_lt_fin {r : ℕ} {p : Fin r → Fin r → Prop} (hsymm : ∀ i j : Fin r, p i j ↔ p j i)
  (h : ∀ i j : Fin r, i < j → p i j) : ∀ i j : Fin r, i ≠ j → p i j := by
    intro i j hij
    wlog hlt : i < j
    push_neg at hlt; symm at hij
    let hlt := lt_of_le_of_ne hlt hij
    specialize this hsymm h j i hij hlt
    rw [hsymm]; exact this

    exact h i j hlt

lemma eval_one_stronglyHomogeneous_decomposition {f p : MvPolynomial α F} {r n : ℕ} (g : Fin r → MvPolynomial α F)
  (hsum : f = ∑ i, g i) (hdot : ∀ i j : Fin r, i < j → Disjoint (orderTypes (g i)) (orderTypes (g j)))
  (hfh : f.IsHomogeneous n) (hph : p.IsHomogeneous n) (hpI : p ∈ symmSpan {f}) (i₀ : Fin r)
  (hg : ∀ i : Fin r, i ≠ i₀ → Disjoint (orderTypes (g i)) (orderTypes p)) (hgz : eval_one p ≠ 0) :
  ∀ i : Fin r, i ≠ i₀ → eval_one (g i) = 0 := by
    apply all_fin_of_lt_fin at hdot; swap; intro i j
    exact disjoint_comm

    sorry

lemma split_orderTypes {f p : MvPolynomial α F} {n : ℕ} (hf : f.IsHomogeneous n) (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) :
  ∃ p' q, f = p' + q ∧ orderTypes p' = orderTypes p ∧ Disjoint (orderTypes p) (orderTypes q) ∧ (eval_one p ≠ 0 → eval_one p' ≠ 0) := by
    sorry

theorem not_psi_of_nonzero_disjoint_orderTypes (hI : IsSingleDegGen I) {p₁ p₂ : MvPolynomial α F}
  (hp₁ : p₁.IsHomogeneous (minDeg I)) (hp₂ : p₂.IsHomogeneous (minDeg I)) (hp₁z : eval_one p₁ ≠ 0) (hp₂z : eval_one p₂ ≠ 0)
  (h : Disjoint (orderTypes p₁) (orderTypes p₂)) : p₁ ∈ I → p₂ ∈ I → ¬IsPrincipalSymmetric I := by
    intro hIp₁ hIp₂
    by_contra! hpsi
    obtain ⟨f, hf, hpsi⟩ := psi_homo_gen_of_singleDegGen hI hpsi
    rw [hpsi] at hIp₁; rw [hpsi] at hIp₂
    obtain ⟨p₁', q₁, hs₁, hoe₁, hod₁, he₁⟩ := split_orderTypes hf hp₁ hIp₁
    obtain ⟨p₂', q₂, hs₂, hoe₂, hod₂, he₂⟩ := split_orderTypes hf hp₂ hIp₂

    have hp12 : Disjoint (orderTypes p₁') (orderTypes p₂') := by
      rw [hoe₁, hoe₂]
      exact h
    have hpq₁ : Disjoint (orderTypes p₁') (orderTypes q₁) := by rw [hoe₁]; exact hod₁
    have hpq₂ : Disjoint (orderTypes p₂') (orderTypes q₂) := by rw [hoe₂]; exact hod₂
    have hpqf₁ : orderTypes p₁' ⊆ orderTypes q₂ := by
      rw [hs₁] at hs₂
      exact orderTypes_subset_add_eq_add hp12 hpq₁ hpq₂ hs₂
    have hpqf₂ : orderTypes p₂' ⊆ orderTypes q₁ := by
      rw [hs₂] at hs₁; rw [disjoint_comm] at hp12
      exact orderTypes_subset_add_eq_add hp12 hpq₂ hpq₁ hs₁


    have hpq1 : Disjoint (orderTypes p₁') (orderTypes (q₂-p₁')) := by sorry
    have hpq2 : Disjoint (orderTypes p₂') (orderTypes (q₂-p₁')) := by
      apply orderTypes_disjoint_sub hpq₂ hpqf₁
    have hpp1 : Disjoint (orderTypes p₂') (orderTypes p₁) := by
      apply Set.disjoint_of_subset_left hpqf₂
      rw [disjoint_comm]
      exact hod₁
    have hq2p : Disjoint (orderTypes (q₂-p₁')) (orderTypes p₁) := by
      rw [← hoe₁, disjoint_comm]
      exact hpq1

    let g := ![p₁', p₂', (q₂-p₁')]
    have hgz : ∀ i : Fin 3, i ≠ 0 → eval_one (g i) = 0 := by
      apply eval_one_stronglyHomogeneous_decomposition g ?_ ?_ hf hp₁ hIp₁ 0 ?_ hp₁z
      rw [Fin.sum_univ_three]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, g]
      ring_nf
      exact hs₂

      intro i j
      fin_cases i; simp;
      fin_cases j; simp
      intro hne
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one, g]
      exact hp12

      intro hne
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
        Fin.reduceFinMk, Matrix.cons_val, g]
      exact hpq1

      fin_cases j; simp [g]; simp [g]
      simp [g]
      exact hpq2

      simp
      intro hj
      apply Nat.add_one_le_of_lt at hj
      let hj2 := j.2
      apply lt_of_le_of_lt hj at hj2
      simp at hj2

      intro i
      fin_cases i; simp
      simp [g]
      exact hpp1

      simp [g]
      exact hq2p

    specialize hgz 1 ?_
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, g] at hgz
    exact he₂ hp₂z hgz
