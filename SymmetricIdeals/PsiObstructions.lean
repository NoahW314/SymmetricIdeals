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

@[simp] lemma eval_one_monomial (d : α →₀ ℕ) (f : F) : eval_one (monomial d f) = f := by
  simp only [eval_one, eval, coe_eval₂Hom, eval₂_monomial, RingHom.id_apply, Finsupp.prod, one_pow,
    Finset.prod_const_one, mul_one]

lemma eval_one_monomial_one_ne_zero (d : α →₀ ℕ) : eval_one (monomial d (1 : F)) ≠ 0 := by
  rw [eval_one_monomial]; exact one_ne_zero

@[simp] lemma eval_one_symm {p : MvPolynomial α F} (σ : Equiv.Perm α) : eval_one (σ • p) = eval_one p := by
  simp [HSMul.hSMul, SMul.smul, eval_one]
  rw [eval_rename]
  congr
@[simp] lemma eval_one_C_mul {p : MvPolynomial α F} {c : F} : eval_one (c • p) = c * eval_one p := by
  simp only [eval_one, smul_eval]

lemma eval_one_zero_invariant {S : Set (MvPolynomial α F)} (h : ∀ p ∈ S, eval_one p = 0) {p : MvPolynomial α F} :
  p ∈ symmSpan S → eval_one p = 0 := by
    intro hp
    unfold symmSpan symmSet at hp
    rw [Ideal.mem_span] at hp
    specialize hp (RingHom.ker eval_one) ?_; swap
    exact hp
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_image] at hq
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨σ, r, hrS, hq⟩ := hq
    rw [← hq]
    rw [eval_one_symm]
    exact h r hrS

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

lemma linear_comb_symm_of_symmSpan_homo {n : ℕ} {f p : MvPolynomial α F} (hf : f.IsHomogeneous n)
  (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) : ∃ c : Equiv.Perm α →₀ F, p = c.sum fun σ b => b • (σ • f) := by
    suffices p ∈ Submodule.span F (Set.range (fun σ : Equiv.Perm α => σ • f)) by
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at this
      obtain ⟨c, this⟩ := this; use c; symm; exact this

    rw [← symmSet_singleton_eq_range, ← homoSubI_span n, homogeneousSubmoduleI,
      Submodule.mem_inf]
    constructor; exact (mem_homogeneousSubmodule n p).mp hp
    rw [Submodule.restrictScalars_mem]
    exact h
    exact symmSet_homo_singleton hf


lemma linear_comb_of_el_symmSpan_homo {n : ℕ} {f p : MvPolynomial α F} (hf : f.IsHomogeneous n)
  (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) : ∃ c : MvPolynomial α F →₀ F,
  ↑c.support ⊆ symmSet {f} ∧ (c.sum fun f' b => b • f') = p := by
    apply Submodule.mem_span_set.mp
    rw [← homoSubI_span n, homogeneousSubmoduleI, Submodule.mem_inf]
    constructor; rw [mem_homogeneousSubmodule]
    exact hp
    rw [Submodule.restrictScalars_mem]
    exact h
    exact symmSet_homo_singleton hf

lemma all_fin_of_lt_fin {r : ℕ} {p : Fin r → Fin r → Prop} (hsymm : ∀ i j : Fin r, p i j ↔ p j i)
  (h : ∀ i j : Fin r, i < j → p i j) : ∀ i j : Fin r, i ≠ j → p i j := by
    intro i j hij
    wlog hlt : i < j
    push_neg at hlt; symm at hij
    let hlt := lt_of_le_of_ne hlt hij
    specialize this hsymm h j i hij hlt
    rw [hsymm]; exact this

    exact h i j hlt

omit [DecidableEq α] in lemma symm_lin_comb_orderTypes {c : Equiv.Perm α →₀ F} {g : MvPolynomial α F} : orderTypes (∑ σ ∈ c.support, c σ • σ • g) ⊆ orderTypes g := by
  apply le_trans orderTypes_sum_subset
  simp only [Finsupp.mem_support_iff, ne_eq, Set.le_eq_subset, Set.iUnion_subset_iff]
  intro σ hσ
  rw [orderTypes_C_mul_ne_zero hσ, orderTypes_symm]

lemma eval_one_stronglyHomogeneous_decomposition {f p : MvPolynomial α F} {r n : ℕ} (g : Fin r → MvPolynomial α F)
  (hsum : f = ∑ i, g i) (hdot : ∀ i j : Fin r, i < j → Disjoint (orderTypes (g i)) (orderTypes (g j)))
  (hfh : f.IsHomogeneous n) (hph : p.IsHomogeneous n) (hpI : p ∈ symmSpan {f}) (i₀ : Fin r)
  (hg : ∀ i : Fin r, i ≠ i₀ → Disjoint (orderTypes (g i)) (orderTypes p)) (hpz : eval_one p ≠ 0) :
  ∀ i : Fin r, i ≠ i₀ → eval_one (g i) = 0 := by
    apply all_fin_of_lt_fin at hdot; swap; intro i j
    exact disjoint_comm
    obtain ⟨c, hc⟩ := linear_comb_symm_of_symmSpan_homo hfh hph hpI
    simp only [Finsupp.sum] at hc
    rw [hsum] at hc
    simp only [Finset.smul_sum] at hc
    rw [Finset.sum_comm] at hc
    have hgi : ∀ i ≠ i₀, ∑ σ ∈ c.support, c σ • σ • g i = 0 := by
      apply zero_of_disjoint_sum hc

      intro i j hij
      apply Disjoint.mono symm_lin_comb_orderTypes symm_lin_comb_orderTypes
      exact hdot i j hij

      intro i hi
      apply Disjoint.mono_left symm_lin_comb_orderTypes
      exact hg i hi
    intro i hi
    have hpi₀ : p = ∑ σ ∈ c.support, c σ • σ • g i₀ := by
      rw [hc];
      apply Finset.sum_eq_single_of_mem
      exact Finset.mem_univ i₀

      intro i hif hi
      exact hgi i hi
    have hp1 : eval_one p = (eval_one (g i₀))*(∑ σ ∈ c.support, c σ) := by
      apply_fun eval_one  at hpi₀
      rw [hpi₀]
      simp only [map_sum, eval_one_C_mul, eval_one_symm, Finset.mul_sum]
      simp only [mul_comm]
    have hgi1 : (eval_one (g i))*(∑ σ ∈ c.support, c σ) = 0 := by
      specialize hgi i hi
      apply_fun eval_one at hgi
      simp only [map_sum, eval_one_C_mul, eval_one_symm, map_zero] at hgi
      rw [← hgi, Finset.mul_sum]
      simp only [mul_comm]

    rw [hp1] at hpz
    apply right_ne_zero_of_mul at hpz
    exact (mul_eq_zero_iff_right hpz).mp hgi1

lemma split_orderTypes {f p : MvPolynomial α F} {n : ℕ} (hf : f.IsHomogeneous n) (hp : p.IsHomogeneous n) (h : p ∈ symmSpan {f}) :
  ∃ p' q, f = p' + q ∧ orderTypes p' = orderTypes p ∧ Disjoint (orderTypes p) (orderTypes q) ∧ (eval_one p ≠ 0 → eval_one p' ≠ 0) := by
    let hfp := linear_comb_symm_of_symmSpan_homo hf hp h
    obtain ⟨c, hc⟩ := hfp

    let S := {d : f.support | (orderType d.1).parts ∈ (orderTypes p)}
    have hfpq : f = (∑ d ∈ S, monomial d (coeff d f)) + (f-(∑ d ∈ S, monomial d (coeff d f))) := by ring
    use (∑ d ∈ S, monomial d (coeff d f))
    use (f-(∑ d ∈ S, monomial d (coeff d f)))
    have hotp : orderTypes (∑ d ∈ S.toFinset, (monomial d.1) (coeff d f)) = orderTypes p := by
      ext s; constructor;
      simp [orderTypes, coeff_sum]
      intro d hd hs
      apply Finset.exists_ne_zero_of_sum_ne_zero at hd
      obtain ⟨x, hxS, hx⟩ := hd
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
      simp [S, orderTypes] at hxS
      rw [hx.1, hs] at hxS
      exact hxS


      intro hs
      simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq,
        coeff_sum, coeff_monomial]
      let hs2 := hs
      simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq] at hs2
      obtain ⟨d, hd, hds⟩ := hs2
      have hsf : s ∈ orderTypes f := by
        suffices orderTypes p ⊆ orderTypes f by exact this hs
        rw [hc]
        simp only [Finsupp.sum]
        exact symm_lin_comb_orderTypes
      simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq] at hsf
      obtain ⟨e, he, hes⟩ := hsf
      use e; constructor; swap; exact hes
      push_neg at he; rw [← mem_support_iff] at he

      rw [Finset.sum_eq_single ⟨e, he⟩]
      simp only [↓reduceIte, ne_eq]
      exact mem_support_iff.mp he

      intro x hxS hxe
      rw [ite_eq_right_iff]
      intro hxe2
      rw [Subtype.coe_eq_iff] at hxe2
      obtain ⟨hef2, hxe2⟩ := hxe2
      simp only [hxe2, ne_eq, not_true_eq_false, S] at hxe

      intro heS
      simp only [Set.toFinset_setOf, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
        true_and, S] at heS
      rw [hes] at heS
      contradiction
    constructor; exact hfpq; constructor
    exact hotp

    have hpq : Disjoint (orderTypes p) (orderTypes (f-∑ d ∈ S.toFinset, (monomial d.1) (coeff d f))) := by
      rw [← Set.subset_compl_iff_disjoint_right]
      intro s
      simp [orderTypes]
      intro d hdc hd e he
      contrapose! he
      rw [coeff_sum]
      by_cases hef : e ∈ f.support

      have hef2 : ⟨e, hef⟩ ∈ S := by
        unfold S
        rw [Set.mem_setOf, Subtype.coe_mk, he, ← hd]
        exact mem_orderTypes hdc
      rw [Finset.sum_eq_single ⟨e, hef⟩]
      simp only [coeff_monomial, ↓reduceIte, sub_self]
      intro x hx hxe
      simp only [coeff_monomial, ite_eq_right_iff]
      contrapose; intro hxf
      rw [Subtype.coe_eq_iff.not]
      push_neg; intro hefs
      exact hxe
      intro hefc; rw [Set.mem_toFinset] at hefc
      contradiction

      rw [notMem_support_iff] at hef
      rw [hef, zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro x hxS
      rw [coeff_monomial, ite_eq_right_iff]
      intro hex
      rw [hex]
      exact hef
    constructor
    exact hpq

    contrapose!
    intro hpz
    have hpsum : p = (∑ σ ∈ c.support, c σ • σ • (∑ d ∈ S.toFinset, (monomial d) (coeff d f))) +
      (∑ σ ∈ c.support, c σ • σ • (f - ∑ d ∈ S.toFinset, (monomial d) (coeff d f))) := by
        rw [← Finset.sum_add_distrib]
        simp only [← smul_add]
        rw [← hfpq]
        simp only [Finsupp.sum] at hc
        exact hc
    rw [hpsum]
    suffices ∑ σ ∈ c.support, c σ • σ • (f - ∑ d ∈ S.toFinset, (monomial d) (coeff d f)) = 0 by
      rw [this, add_zero, eval_one, eval_sum]
      apply Finset.sum_eq_zero; intro σ hσ
      rw [smul_eval]
      apply mul_eq_zero_of_right
      rw [← hpz]
      rw [← eval_one_symm σ]
      rfl

    apply zero_of_disjoint_add hpsum
    apply Disjoint.mono_right symm_lin_comb_orderTypes hpq

    apply Disjoint.mono_left symm_lin_comb_orderTypes
    apply Disjoint.mono_right symm_lin_comb_orderTypes
    rw [hotp]
    exact hpq

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
      exact orderTypes_subset_of_add_eq_add hp12 hpq₁ hpq₂ hs₂
    have hpqf₂ : orderTypes p₂' ⊆ orderTypes q₁ := by
      rw [hs₂] at hs₁; rw [disjoint_comm] at hp12
      exact orderTypes_subset_of_add_eq_add hp12 hpq₂ hpq₁ hs₁


    have hpq1 : Disjoint (orderTypes p₁') (orderTypes (q₂-p₁')) := by
      apply disjoint_sub_orderTypes_of_add_eq_add hp12 hpq₁
      rw [← hs₁, ← hs₂]
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
