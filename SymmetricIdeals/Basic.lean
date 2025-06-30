import Mathlib

variable {F : Type*} [CommSemiring F] -- later this will be a field
variable {α : Type*} -- later this will be finite

open Equiv (Perm)
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable
instance SymmetricAction : MulSemiringAction (Perm α) (MvPolynomial α F) where
  smul σ p := rename σ p
  one_smul := by intro p; apply rename_id_apply
  mul_smul := by
    intro σ τ p; simp only [HSMul.hSMul]
    have hcoecomp : ⇑(σ * τ) = ⇑σ ∘ ⇑τ := by rfl
    rw [hcoecomp, ← rename_comp_rename]
    rfl
  smul_zero := by intro σ; simp only [HSMul.hSMul]; rfl
  smul_add := by
    intro σ p q; simp only [HSMul.hSMul]
    exact map_add (rename ⇑σ) p q
  smul_one := by
    intro σ; simp only [HSMul.hSMul];
    exact map_one (rename ⇑σ)
  smul_mul := by
    intro σ p q; simp only [HSMul.hSMul]
    exact MulHomClass.map_mul (rename ⇑σ) p q
lemma symmAct_def (σ : Perm α) (p : MvPolynomial α F) : σ • p = rename σ p := by rfl

lemma homo_symmAct (σ : Perm α) {p : MvPolynomial α F} {n : ℕ} (h : p.IsHomogeneous n) : (σ • p).IsHomogeneous n := by
  rw [symmAct_def]
  apply IsHomogeneous.rename_isHomogeneous h

@[simp] lemma homoComp_symmAct {σ : Perm α} {p : MvPolynomial α F} {n : ℕ} : σ • (homogeneousComponent n p) =
  homogeneousComponent n (σ • p) := by
    rw [symmAct_def, symmAct_def]
    ext d
    rw [coeff_homogeneousComponent]
    have he : ∃ e : α →₀ ℕ, Finsupp.mapDomain σ e = d := by
      use Finsupp.mapDomain σ.symm d
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
    obtain ⟨e, he⟩ := he
    nth_rw 1 [← he]
    rw [coeff_rename_mapDomain σ (Equiv.injective σ), coeff_homogeneousComponent]
    have hed : e.degree = d.degree := by
      rw [← he]
      simp only [Finsupp.degree, Finsupp.mapDomain_equiv_apply]
      apply Finset.sum_bijective σ (Equiv.bijective σ)
      simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.mapDomain_equiv_apply,
        Equiv.symm_apply_apply, implies_true]
      simp only [Finsupp.mem_support_iff, ne_eq, Equiv.symm_apply_apply, implies_true]
    by_cases hd : d.degree = n
    rw [hd] at hed
    simp only [hed, ↓reduceIte, hd]
    rw [← he, coeff_rename_mapDomain σ (Equiv.injective σ)]

    have hed : ¬e.degree = n := by exact Lean.Grind.ne_of_ne_of_eq_left hed hd
    simp only [hed, ↓reduceIte, hd]

lemma symm_monomial {σ : Equiv.Perm α} {d : α →₀ ℕ} {c : F} : σ • (monomial d c) =
  monomial (Finsupp.mapDomain σ d) c := by
    simp only [symmAct_def, rename_monomial]

noncomputable def IsSymmetricI (I : Ideal (MvPolynomial α F)) :=
  ∀ σ : Perm α, ∀ f ∈ I, σ • f ∈ I

lemma is_symm_iff_stable_image {I : Ideal (MvPolynomial α F)} : IsSymmetricI I ↔ ∀ σ : Perm α,
  Ideal.map (rename σ) I = I := by
    constructor; intro h σ
    ext f; constructor; intro hi
    apply (Ideal.mem_map_of_equiv (renameEquiv F σ) f).mp at hi
    obtain ⟨g, hi, hg⟩ := hi
    rw [← hg]
    apply h σ g hi

    intro hi
    rw [← (renameEquiv F σ).right_inv f]
    apply Ideal.mem_map_of_mem
    exact h σ⁻¹ f hi

    intro h σ f hi
    specialize h σ
    rw [← h]
    apply Ideal.mem_map_of_mem; exact hi

def symmSet (S : Set (MvPolynomial α F)) : Set (MvPolynomial α F) := ⋃ σ : Perm α, ((σ • .) '' S)
def symmSpan (S : Set (MvPolynomial α F)) : Ideal (MvPolynomial α F) := Ideal.span (symmSet S)

@[simp] lemma mem_symmSet_singleton {p q : MvPolynomial α F} : q ∈ symmSet {p} ↔ ∃ σ : Perm α, σ • p = q := by
  simp only [symmSet, Set.image_singleton, Set.iUnion_singleton_eq_range, Set.mem_range]

@[simp] lemma mem_symmSet_singleton_of_perm {p : MvPolynomial α F} {σ : Perm α} : σ • p ∈ symmSet {p} := by
  rw [mem_symmSet_singleton]; use σ

@[simp] lemma mem_symmSet_singleton_self {p : MvPolynomial α F} : p ∈ symmSet {p} := by
  rw [mem_symmSet_singleton]
  use 1; apply one_smul

@[simp] lemma symmSet_symm {S : Set (MvPolynomial α F)} {σ : Perm α} : (rename σ) '' (symmSet S) = symmSet S := by
  ext f; constructor
  intro h
  rw [Set.mem_image] at h
  obtain ⟨g, hs, hg⟩ := h
  unfold symmSet at hs; unfold symmSet
  rw [Set.mem_iUnion] at hs; rw [Set.mem_iUnion]
  obtain ⟨τ, hs⟩ := hs; use σ * τ
  rw [Set.mem_image] at hs; rw[Set.mem_image]
  obtain ⟨p, hs, hp⟩ := hs; use p
  constructor; exact hs
  rw [mul_smul, hp]
  exact hg

  intro h; rw [Set.mem_image]
  use σ⁻¹ • f; constructor; swap; exact smul_inv_smul σ f
  unfold symmSet at h; unfold symmSet
  rw [Set.mem_iUnion] at h; rw [Set.mem_iUnion]
  obtain ⟨τ, h⟩ := h; use σ⁻¹ * τ
  rw [Set.mem_image] at h; rw [Set.mem_image]
  obtain ⟨g, hs, hg⟩ := h; use g
  constructor; exact hs
  rw [mul_smul, hg]

@[simp] lemma symmSet_zero : symmSet {(0 : MvPolynomial α F)} = {0} := by
  simp only [symmSet, Set.image_singleton, smul_zero, Set.iUnion_singleton_eq_range, Set.range_const]
@[simp] lemma symmSet_one : symmSet {(1 : MvPolynomial α F)} = {1} := by
  simp only [symmSet, Set.image_singleton, smul_one, Set.iUnion_singleton_eq_range, Set.range_const]

lemma zero_notMem_nonzero_symmSet {f : MvPolynomial α F} (h : f ≠ 0) : 0 ∉ symmSet {f} := by
  contrapose! h
  unfold symmSet at h
  rw [Set.mem_iUnion] at h
  obtain ⟨σ, h⟩ := h
  rw [Set.image_singleton, Set.mem_singleton_iff] at h
  symm at h
  exact (smul_eq_zero_iff_eq σ).mp h

lemma symmSet_homo_singleton {n : ℕ} {p : MvPolynomial α F} (h : p.IsHomogeneous n) : symmSet {p} ⊆ (homogeneousSubmodule α F n) := by
  intro q hq; rw [mem_symmSet_singleton] at hq
  obtain ⟨σ, hq⟩ := hq
  rw [← hq]; simp only [SetLike.mem_coe, mem_homogeneousSubmodule]
  apply homo_symmAct σ h

lemma symmSet_singleton_eq_range {p : MvPolynomial α F} : symmSet {p} = Set.range (fun σ : Equiv.Perm α => σ • p) := by
  simp only [symmSet, Set.image_singleton, Set.iUnion_singleton_eq_range]

lemma symmSpan_symm {S : Set (MvPolynomial α F)} : IsSymmetricI (symmSpan S) := by
  apply is_symm_iff_stable_image.mpr
  intro σ; unfold symmSpan
  rw [Ideal.map_span, symmSet_symm]
@[simp] lemma symmSpan_zero : symmSpan {(0 : MvPolynomial α F)} = ⊥ := by
  unfold symmSpan
  rw [symmSet_zero, Ideal.span_singleton_eq_bot]
@[simp] lemma symmSpan_one : symmSpan {(1 : MvPolynomial α F)} = ⊤ := by
  rw [symmSpan, symmSet_one, Ideal.span_singleton_eq_top]
  exact isUnit_one

lemma mem_symmSpan_self {p : MvPolynomial α F} : p ∈ symmSpan {p} := by
  apply Submodule.subset_span
  exact mem_symmSet_singleton_self

lemma symmSpan_sum_le_sup_symmSpan {X : Type*} {S : Finset X} {g : S → MvPolynomial α F} :
  symmSpan {∑ a, g a} ≤ ⨆ a, symmSpan {g a} := by
    unfold symmSpan Ideal.span
    rw [← Submodule.span_iUnion]
    apply Submodule.span_le.mpr
    intro p hp; rw [mem_symmSet_singleton] at hp;
    obtain ⟨σ, hp⟩ := hp
    rw [← hp, Finset.smul_sum]
    apply sum_mem; intro a ha
    apply Submodule.subset_span
    rw [Set.mem_iUnion];
    use a; exact mem_symmSet_singleton_of_perm

lemma symmSpan_singleton_le_of_mem {p q : MvPolynomial α F} (h : q ∈ symmSpan {p}) :
  symmSpan {q} ≤ symmSpan {p} := by
    apply Ideal.span_le.mpr
    intro r hr; rw [mem_symmSet_singleton] at hr
    obtain ⟨σ, hr⟩ := hr; rw [← hr]
    apply symmSpan_symm σ
    exact h


noncomputable def IsPrincipalSymmetric (I : Ideal (MvPolynomial α F)) := ∃ f : MvPolynomial α F,
  I = symmSpan {f}

lemma psi_is_symm {I : Ideal (MvPolynomial α F)} : IsPrincipalSymmetric I → IsSymmetricI I := by
  intro h
  obtain ⟨f, h⟩ := h
  rw [h]
  exact symmSpan_symm

lemma top_is_psi : IsPrincipalSymmetric (⊤ : Ideal (MvPolynomial α F)) := by
  use 1; symm; exact symmSpan_one
lemma bot_is_psi : IsPrincipalSymmetric (⊥ : Ideal (MvPolynomial α F)) := by
  use 0; symm; exact symmSpan_zero
