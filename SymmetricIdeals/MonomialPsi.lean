import Mathlib
import SymmetricIdeals.PsiObstructions

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}
attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

variable [DecidableEq α]

lemma span_orderTypeComponent_le_symmSpan {p : MvPolynomial α F} {a : Multiset ℕ}
  (ha : a ∈ orderTypes p) (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : F)) '' S)) :
  Ideal.span (orderTypeComponent α F a) ≤ symmSpan {p} := by
    simp only [orderTypes, ne_eq, Set.mem_image, Set.mem_setOf_eq] at ha
    obtain ⟨d, hdz, hda⟩ := ha
    suffices (monomial d (1 : F)) ∈ symmSpan {p} by
      apply symmSpan_singleton_le_of_mem at this
      rw [monomial_symmSpan_orderTypeComponent, hda] at this
      exact this
    obtain ⟨S, hm⟩ := hm
    have hp : p ∈ symmSpan {p} := mem_symmSpan_self
    rw [hm, mem_ideal_span_monomial_image] at hp
    rw [hm, mem_ideal_span_monomial_image]
    simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      Decidable.not_not, forall_eq']
    rw [← ne_eq, ← mem_support_iff] at hdz
    exact hp d hdz

lemma symmSpan_eq_span_orderTypeComponent {p : MvPolynomial α F} {a : Multiset ℕ}
  (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : F)) '' S))
  (hp : stronglyHomogeneous p a) (hpz : p ≠ 0) : symmSpan {p} = Ideal.span (orderTypeComponent α F a) := by
    apply antisymm (subset_orderTypeComponent hp)
    apply span_orderTypeComponent_le_symmSpan ?_ hm
    rw [orderTypes_singleton_iff_stronglyHomogeneous hpz] at hp
    rw [hp]; rfl

lemma le_symmSpan_of_le_sup_symmSpan {S : Finset (Multiset ℕ)} {a : S} {g : S → MvPolynomial α F}
  (hdis : ∀ a b : S, a ≠ b → Disjoint (orderTypes (g a)) (orderTypes (g b)))
  (hag : orderTypes (g a) = {a.1}) (hgh : ∀ b, (g b).IsHomogeneous (a.1.sum)) :
  Ideal.span (orderTypeComponent α F a) ≤ ⨆ b, symmSpan {g b} →
  Ideal.span (orderTypeComponent α F a) ≤ symmSpan {g a} := by
    intro h
    apply Ideal.span_le.mpr
    intro p hp
    by_cases hpz : p = 0
    rw [hpz, symmSpan]; simp only [SetLike.mem_coe, Submodule.zero_mem]

    let hpsh := hp
    simp only [SetLike.mem_coe, mem_orderTypeComponent] at hpsh
    apply Ideal.subset_span at hp
    apply h at hp
    have hp : p ∈ ⨆ b, Submodule.span F (symmSet {g b}) := by
      have hb : ∀ b, Submodule.span F (symmSet {g b}) = homogeneousSubmoduleI a.1.sum (Ideal.span (symmSet {g b})) := by
        intro b; symm
        apply homoSubI_span
        apply symmSet_homo_singleton (hgh b)
      simp only [hb]
      rw [← homoSubI_iSup, homogeneousSubmoduleI, Submodule.mem_inf]
      constructor; rw [mem_homogeneousSubmodule]
      exact isHomogeneous_of_stronglyHomogeneous a hpsh
      rw [Submodule.restrictScalars_mem]
      unfold symmSpan at hp
      exact hp

      intro b
      rw [← symmSpan]
      apply single_deg_gen_homo
      apply singleDegGen_of_symmSpan (hgh b)
    rw [Submodule.mem_iSup_iff_exists_finset] at hp
    obtain ⟨s, hp⟩ := hp
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hp
    obtain ⟨μ, hp⟩ := hp
    suffices ∀ i ∈ s, i ≠ a → (μ i).1 = 0 by
      rw [Finset.sum_eq_ite a this] at hp
      rw [← hp]
      by_cases has : a ∈ s
      simp only [has, ↓reduceIte, SetLike.mem_coe, symmSpan]
      let hμ := (μ a).2
      apply Submodule.span_subset_span F (MvPolynomial α F) at hμ
      exact hμ

      simp only [has, ↓reduceIte, SetLike.mem_coe, Submodule.zero_mem]

    intro i his hia
    suffices orderTypes ((μ i).1) ⊆ (orderTypes p) ∩ (orderTypes (g i))  by
      rw [orderTypes_singleton_iff_stronglyHomogeneous hpz] at hpsh
      rw [hpsh, ← hag, Set.inter_comm, Disjoint.inter_eq (hdis i a hia)] at this
      rw [Set.subset_empty_iff, empty_orderTypes_iff_zero] at this
      exact this
    have hjg : ∀ j ∈ s, orderTypes (μ j).1 ⊆ orderTypes (g j) := by
      intro j hjs
      let hμ := (μ j).2
      rw [Submodule.mem_span_iff_exists_finset_subset] at hμ
      obtain ⟨f, t, ht, hf, hμ⟩ := hμ
      rw [← hμ]
      apply subset_trans orderTypes_sum_subset
      simp only [Set.iUnion_subset_iff]
      intro q hq
      apply subset_trans orderTypes_C_mul
      apply ht at hq
      rw [mem_symmSet_singleton] at hq
      obtain ⟨σ, hq⟩ := hq
      rw [← hq]
      exact orderTypes_symm_subset
    apply Set.subset_inter ?_ (hjg i his)
    rw [← hp, orderTypes_sum]
    exact Set.subset_iUnion₂_of_subset i his fun ⦃a⦄ a ↦ a

    intro x y hxs hys hxy
    apply Disjoint.mono (hjg x hxs) (hjg y hys)
    exact hdis x y hxy


theorem stronglyHomogeneous_of_homogeneous {p : MvPolynomial α F}
  (hm : ∃ S : Set (α →₀ ℕ), symmSpan {p} = Ideal.span ((fun d => monomial d (1 : F)) '' S)) (n : ℕ) :
  p.IsHomogeneous n → ∃ a : Multiset ℕ, stronglyHomogeneous p a := by
    intro hp
    by_cases hpz : p = 0
    use 0; rw [hpz]; exact zero_stronglyHomogeneous 0
    let S := Finset.image orderType p.support
    let g : S → MvPolynomial α F := fun a => ∑ d ∈ {d ∈ p.support | orderType d = a}, monomial d (coeff d p)

    have hgp : p = ∑ a, g a := by
      ext d; rw [coeff_sum]; unfold g
      simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq',
        Finset.mem_filter, mem_support_iff, ne_eq]
      rw [Finset.sum_ite]
      simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.sum_const,
        nsmul_eq_mul, not_and, mul_zero, add_zero]
      by_cases hdpz : coeff d p = 0
      rw [hdpz, mul_zero]

      suffices Finset.card {x : S | d ∈ {e ∈ p.support | orderType e = x}} = 1 by
        rw [this]; simp only [Nat.cast_one, one_mul]
      rw [Finset.card_eq_one]
      have hdS : orderType d ∈ S := by
        unfold S
        simp only [Finset.mem_image, mem_support_iff, ne_eq]
        use d
      use ⟨orderType d, hdS⟩
      rw [Finset.eq_singleton_iff_unique_mem]; constructor
      simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.univ_eq_attach,
        Finset.mem_attach, and_true, true_and]
      exact hdpz

      intro x hx
      simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.univ_eq_attach,
        Finset.mem_attach, true_and] at hx
      apply And.right at hx; symm at hx
      rw [Subtype.coe_eq_iff] at hx
      obtain ⟨_, hx⟩ := hx
      exact hx

    have hgsh : ∀ a, stronglyHomogeneous (g a) a := by
      intro a; unfold stronglyHomogeneous
      intro d hd; unfold g at hd
      simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, mem_support_iff,
        ne_eq, ite_eq_right_iff, and_imp, Classical.not_imp] at hd
      exact hd.2.1
    have hmdp : ∀ a : S, minDeg (symmSpan {p}) = a.1.sum := by
      intro a
      rw [minDeg_symmSpan hp hpz]
      let ha := a.2; unfold S at ha
      rw [Finset.mem_image] at ha
      obtain ⟨d, hd⟩ := ha
      rw [← hd.2, orderType_sum_eq_degree]
      rw [mem_support_iff] at hd
      rw [← hp hd.1]
      simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
        LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
        LinearMap.id_coe, id_eq, smul_eq_mul, mul_one, Finsupp.degree]
    have hgh : ∀ a, (g a).IsHomogeneous (minDeg (symmSpan {p})) := by
      intro a
      rw [hmdp a]
      exact isHomogeneous_of_stronglyHomogeneous a (hgsh a)
    have hgz : ∀ a, g a ≠ 0 := by
      intro a; rw [ne_zero_iff]
      let ha := a.2; unfold S at ha
      rw [Finset.mem_image] at ha
      obtain ⟨d, hd⟩ := ha
      rw [mem_support_iff] at hd
      use d; unfold g
      simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, mem_support_iff,
        ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte]
    have hgd : ∀ a b, a ≠ b → Disjoint (orderTypes (g a)) (orderTypes (g b)) := by
      intro a b hab
      rw [(orderTypes_singleton_iff_stronglyHomogeneous (hgz a)).mp (hgsh a)]
      rw [(orderTypes_singleton_iff_stronglyHomogeneous (hgz b)).mp (hgsh b)]
      rw [Set.disjoint_singleton, Subtype.coe_ne_coe]
      exact hab
    have hgi : ∀ a, g a ∈ symmSpan {p} := by
      intro a; unfold g symmSpan
      apply Submodule.sum_mem
      intro d hd; simp only [Finset.mem_filter] at hd
      suffices monomial d 1 ∈ Ideal.span (symmSet {p}) by
        apply Submodule.smul_mem _ (C (coeff d p)) at this
        simp only [C_eq_smul_one, smul_eq_mul, Algebra.smul_mul_assoc, one_mul, smul_monomial,
          mul_one] at this
        exact this
      obtain ⟨T, hT⟩ := hm; unfold symmSpan at hT; rw [hT]
      have hpI : p ∈ symmSpan {p} := mem_symmSpan_self
      rw [symmSpan, hT, mem_ideal_span_monomial_image] at hpI
      rw [mem_ideal_span_monomial_image]
      simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        Decidable.not_not, forall_eq']
      exact hpI d hd.1
    have hgot : ∀ a, symmSpan {g a} = Ideal.span (orderTypeComponent α F a) := by
      intro a
      apply span_orderTypeComponent_le_symmSpan (mem_orderTypes_iff_image_support.mpr a.2) at hm
      rw [hgp] at hm
      apply le_trans' symmSpan_sum_le_sup_symmSpan at hm
      apply le_symmSpan_of_le_sup_symmSpan hgd at hm
      symm; apply antisymm hm

      apply subset_orderTypeComponent
      exact hgsh a

      rw [← orderTypes_singleton_iff_stronglyHomogeneous (hgz a)]
      exact hgsh a
      rw [← hmdp a]
      exact hgh
    have hgeo : ∀ a, eval_one (g a) ≠ 0 := by
      intro a; specialize hgot a
      contrapose! hgot
      apply ne_of_lt
      apply strict_subset_orderType (hgsh a) (hgz a) hgot
    suffices S.card ≤ 1 by
      rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
      rcases this with h0|h1
      simp only [Finset.card_eq_zero, Finset.image_eq_empty, support_eq_empty, S] at h0
      contradiction

      rw [Finset.card_eq_one] at h1; unfold S at h1
      obtain ⟨a, h1⟩ := h1; use a
      rw [orderTypes_singleton_iff_stronglyHomogeneous hpz]
      apply_fun (fun x => x.toSet) at h1
      simp only [Finset.coe_image, Finset.coe_singleton] at h1
      rw [← h1, orderTypes];
      suffices {d | coeff d p ≠ 0} = p.support by rw [this]
      ext d; rw [Set.mem_setOf];
      simp only [ne_eq, Finset.mem_coe, mem_support_iff]

    by_contra! hS
    rw [← Fintype.card_coe, Fintype.one_lt_card_iff] at hS
    obtain ⟨a, b, hab⟩ := hS
    suffices ¬IsPrincipalSymmetric (symmSpan {p}) by apply this; use p
    apply not_psi_of_nonzero_disjoint_orderTypes (singleDegGen_of_symmSpan hp) (hgh a) (hgh b) (hgeo a) (hgeo b)
    exact hgd a b hab; exact hgi a; exact hgi b

theorem monomial_iff_symmSpan_monomial (h : IsPrincipalSymmetric I) (hI : IsSingleDegGen I)
  (hIB : I ≠ ⊥) : (∃ S : Set (α →₀ ℕ), I = Ideal.span ((fun d => monomial d (1 : F)) '' S)) ↔
  ∃ d : α →₀ ℕ, I = symmSpan {monomial d (1 : F)} := by
    constructor; intro hm
    obtain ⟨p, hph, hp⟩ := psi_homo_gen_of_singleDegGen hI h
    rw [hp] at hm
    apply stronglyHomogeneous_of_homogeneous hm (minDeg I) at hph
    obtain ⟨a, hsh⟩ := hph
    let hot := symmSpan_eq_span_orderTypeComponent hm hsh
    rw [hp, hot]
    apply exists_monomial_symmSpan_orderTypeComponent
    use p; constructor; swap; exact hsh
    contrapose! hIB
    rw [hp, hIB, symmSpan_zero]

    contrapose! hIB; rw [hp, hIB, symmSpan_zero]

    intro hm
    obtain ⟨d, hd⟩ := hm
    use Set.range (fun σ : Equiv.Perm α => (Finsupp.mapDomain σ d))
    rw [hd, symmSpan, symmSet]; congr
    ext p; simp only [Set.image_singleton, symm_monomial, Set.iUnion_singleton_eq_range,
      Set.mem_range, Set.mem_image, exists_exists_eq_and]
