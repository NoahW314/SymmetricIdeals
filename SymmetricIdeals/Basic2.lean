import Mathlib
import SymmetricIdeals.GradedMinimalGenerators

variable {F : Type*} [CommSemiring F] -- later this will be a field
variable {α : Type*} -- later this will be finite

open Equiv (Perm)
open MvPolynomial

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

lemma symmSet_symm {S : Set (MvPolynomial α F)} {σ : Perm α} : (rename σ) '' (symmSet S) = symmSet S := by
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

lemma symmSpan_symm {S : Set (MvPolynomial α F)} : IsSymmetricI (symmSpan S) := by
  apply is_symm_iff_stable_image.mpr
  intro σ; unfold symmSpan
  rw [Ideal.map_span, symmSet_symm]

noncomputable def IsPrincipalSymmetric (I : Ideal (MvPolynomial α F)) := ∃ f : MvPolynomial α F,
  I = symmSpan {f}

lemma psi_is_symm {I : Ideal (MvPolynomial α F)} : IsPrincipalSymmetric I → IsSymmetricI I := by
  intro h
  obtain ⟨f, h⟩ := h
  rw [h]
  exact symmSpan_symm

variable {α : Type*} [Finite α]

open Classical
lemma psi_mgs_factorial {I : Ideal (MvPolynomial α F)} : IsPrincipalSymmetric I →
  (μ (MvPolynomial α F) I ≤ (Nat.card α).factorial) := by
    intro h; obtain ⟨f, h⟩ := h
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
    use S; constructor; rfl
    rw [h]; unfold symmSpan; congr
    simp only [Set.coe_toFinset, S, S']
