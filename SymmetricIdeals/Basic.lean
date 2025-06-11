import Mathlib
import SymmetricIdeals.GradedMinimalGenerators


variable {𝕜 : Type*} [hkf : Field 𝕜]
variable {ι : Type*} {α : Finset ι}


noncomputable
def expPerm (σ : Equiv.Perm α) := fun (s : α →₀ ℕ) => (Finsupp.equivFunOnFinite.invFun (s ∘ σ))

lemma expPerm_inv (σ : Equiv.Perm α) (s : α →₀ ℕ) : (expPerm σ (expPerm σ⁻¹ s)) = s := by
  simp only [expPerm, Equiv.invFun_as_coe, Finsupp.coe_equivFunOnFinite_symm, Function.comp_assoc,
    (Equiv.eq_symm_comp σ⁻¹ (⇑σ) id).mp rfl, CompTriple.comp_eq, Finsupp.equivFunOnFinite_symm_coe]
lemma expPerm_inv' (σ : Equiv.Perm α) (s : α →₀ ℕ) : (expPerm σ⁻¹ (expPerm σ s)) = s := by
  nth_rw 2 [← expPerm_inv σ⁻¹ s]; rw [inv_inv]
lemma expPerm_one (s : α →₀ ℕ) : (expPerm 1 s) = s := by
  simp only [expPerm, Equiv.Perm.coe_one, CompTriple.comp_eq, Equiv.invFun_as_coe,
    Finsupp.equivFunOnFinite_symm_coe]
lemma expPerm_mul (σ τ : Equiv.Perm α) (s : α →₀ ℕ) :
  (expPerm σ (expPerm τ s)) = expPerm (τ * σ) s := by
    simp only [expPerm, Equiv.invFun_as_coe, Finsupp.coe_equivFunOnFinite_symm, Function.comp_assoc,
      Equiv.Perm.coe_mul]
lemma expPerm_zero (σ : Equiv.Perm α) : expPerm σ 0 = 0 := by
  unfold expPerm; ext s;
  simp only [Finsupp.coe_zero, Pi.zero_comp, Equiv.invFun_as_coe,
    Finsupp.equivFunOnFinite_symm_apply_toFun, Pi.zero_apply]
lemma expPerm_zero_iff (σ : Equiv.Perm α) (s : α →₀ ℕ)
  : expPerm σ s = 0 ↔ s = 0 := by
    constructor; intro h
    apply_fun (expPerm σ⁻¹) at h
    rw [expPerm_inv', expPerm_zero] at h
    exact h

    intro h; rw [h]; exact expPerm_zero σ
lemma expPerm_zero_iff' (σ : Equiv.Perm α) (s : α →₀ ℕ)
  : 0 = expPerm σ s ↔ 0 = s := by
    constructor; intro h; symm; symm at h; exact (expPerm_zero_iff σ s).mp h
    intro h; symm; symm at h; exact (expPerm_zero_iff σ s).mpr h

lemma expPerm_add (σ : Equiv.Perm α) (s t : α →₀ ℕ) :
  (expPerm σ s)+(expPerm σ t) = expPerm σ (s+t) := by
    unfold expPerm
    exact (Equiv.apply_eq_iff_eq_symm_apply Finsupp.equivFunOnFinite).mp rfl

noncomputable
def act (α : Finset ι) (𝕜 : Type*) [Field 𝕜] (σ : Equiv.Perm α) (p : MvPolynomial α 𝕜) : MvPolynomial α 𝕜
  := ⟨
    (Finset.image (expPerm σ⁻¹) p.support),
    fun s => p.2 ((expPerm σ) s),
    by
      intro s; constructor; intro h
      rw [Finset.mem_image] at h
      simp only
      obtain ⟨t, hps, h⟩ := h
      apply (p.mem_support_toFun (expPerm σ s)).mp
      rw [← h, expPerm_inv]
      exact hps

      intro h; simp only at h
      rw [Finset.mem_image]
      use (expPerm σ s); constructor
      apply (p.mem_support_toFun (expPerm σ s)).mpr h
      exact expPerm_inv' σ s
    ⟩
abbrev permActs (α : Finset ι) [DecidableEq α] (𝕜 : Type*) [Field 𝕜] := Equiv.Perm α
lemma act_coeff (σ : Equiv.Perm α) (p : MvPolynomial α 𝕜) (s : α →₀ ℕ) :
  MvPolynomial.coeff s ((act α 𝕜 σ) p) = MvPolynomial.coeff (expPerm σ s) p := by
    simp only [MvPolynomial.coeff, DFunLike.coe, act]
variable {ι : Type*} {α : Finset ι} [DecidableEq α]
lemma act_monomial (σ : Equiv.Perm α) (s : α →₀ ℕ) :
  (act α 𝕜 σ) (MvPolynomial.monomial s 1) = MvPolynomial.monomial (expPerm σ⁻¹ s) 1 := by
    apply MvPolynomial.ext
    intro t
    rw [act_coeff, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    have hst : s = expPerm σ t ↔ expPerm σ⁻¹ s = t := by
      constructor; intro h
      apply_fun expPerm σ⁻¹ at h
      rw [expPerm_inv'] at h; exact h
      intro h
      apply_fun expPerm σ  at h
      rw [expPerm_inv] at h; exact h
    simp only [hst]
lemma actInj {σ τ : Equiv.Perm α} : act α 𝕜 σ = act α 𝕜 τ → σ = τ := by
  intro h; ext x
  let sx : α →₀ ℕ := Finsupp.single x 1
  let p := MvPolynomial.monomial sx (1 : 𝕜)
  have hp : (act α 𝕜 σ) p = (act α 𝕜 τ) p := by rw [h]
  let σx : α →₀ ℕ := Finsupp.single (σ x) 1
  let τx : α →₀ ℕ := Finsupp.single (τ x) 1
  suffices σx = τx by
    rw [Finsupp.single_eq_single_iff] at this
    simp only [and_true, one_ne_zero, and_self, or_false] at this
    apply Subtype.coe_inj.mpr this
  have hσ : σx = expPerm σ⁻¹ sx := by
    ext y; simp only [expPerm, Equiv.invFun_as_coe, Finsupp.equivFunOnFinite_symm_apply_toFun,
      Function.comp_apply, σx, sx]
    by_cases hy : x = σ⁻¹ y
    simp only [hy, Equiv.Perm.apply_inv_self, Finsupp.single_eq_same]

    have hy' : σ x ≠ y := by
      contrapose! hy
      apply_fun σ⁻¹ at hy
      rw [Equiv.Perm.inv_apply_self] at hy
      exact hy
    simp only [ne_eq, hy, hy', not_false_eq_true, Finsupp.single_eq_of_ne]
  have hpσ : (act α 𝕜 σ) p = MvPolynomial.monomial σx 1 := by rw [hσ, ← act_monomial]
  have hτ : τx = expPerm τ⁻¹ sx := by
    ext y; simp only [expPerm, Equiv.invFun_as_coe, Finsupp.equivFunOnFinite_symm_apply_toFun,
      Function.comp_apply, τx, sx]
    by_cases hy : x = τ⁻¹ y
    simp only [hy, Equiv.Perm.apply_inv_self, Finsupp.single_eq_same]

    have hy' : τ x ≠ y := by
      contrapose! hy
      apply_fun τ⁻¹ at hy
      rw [Equiv.Perm.inv_apply_self] at hy
      exact hy
    simp only [ne_eq, hy, hy', not_false_eq_true, Finsupp.single_eq_of_ne]
  have hpτ : (act α 𝕜 τ) p = MvPolynomial.monomial τx 1 := by rw [hτ, ← act_monomial]
  rw [hpσ, hpτ, MvPolynomial.monomial_eq_monomial_iff] at hp
  simp only [and_true, one_ne_zero, and_self, or_false] at hp
  exact hp
noncomputable
instance instFunLike : FunLike (permActs α 𝕜) (MvPolynomial α 𝕜) (MvPolynomial α 𝕜) where
  coe := fun σ => act α 𝕜 σ
  coe_injective' := by
    intro σ τ h
    exact actInj h
instance instAddHom : AddMonoidHomClass (permActs α 𝕜) (MvPolynomial α 𝕜) (MvPolynomial α 𝕜) where
  map_add := by
    intro σ p q
    ext s; rfl
  map_zero := by
    intro σ; ext s; rfl

variable {ι : Type*} {α : Finset ι} [DecidableEq α]

noncomputable
instance SymmetricAction : MulSemiringAction (Equiv.Perm α) (MvPolynomial α 𝕜) where
  smul := act α 𝕜
  one_smul := by
    intro p; ext s; simp only [HSMul.hSMul]
    rw [act_coeff, expPerm_one]
  mul_smul := by
    intro σ τ p; ext s
    unfold MvPolynomial.coeff DFunLike.coe HSMul.hSMul
    rfl
  smul_zero := by
    intro σ; ext s
    unfold MvPolynomial.coeff DFunLike.coe HSMul.hSMul
    rfl
  smul_add := by
    intro σ p q; ext s
    unfold MvPolynomial.coeff DFunLike.coe HSMul.hSMul
    rfl
  smul_one := by
    intro σ; ext s
    simp only [HSMul.hSMul]
    rw [act_coeff, MvPolynomial.coeff_one, MvPolynomial.coeff_one]
    simp only [expPerm_zero_iff']
  smul_mul := by
    intro σ p q; ext s
    rw [MvPolynomial.coeff_mul]
    simp only [HSMul.hSMul, instHSMul, act_coeff]
    rw [MvPolynomial.coeff_mul]
    let β := (α →₀ ℕ)
    let e : β × β  ↪ β × β := ⟨fun x => (expPerm σ x.1, expPerm σ x.2), by
      intro x y
      simp only [Prod.mk.injEq, and_imp]
      intro h1 h2
      apply_fun (expPerm σ⁻¹) at h1; apply_fun (expPerm σ⁻¹) at h2
      rw [expPerm_inv', expPerm_inv'] at h1; rw [expPerm_inv', expPerm_inv'] at h2
      apply Prod.mk_inj.mpr; constructor
      exact h1; exact h2
      ⟩
    have hed : ∀ x : β × β, e x = (expPerm σ x.1, expPerm σ x.2) := by intro x; rfl
    have hes : Finset.antidiagonal (expPerm σ s) = (Finset.map e (Finset.antidiagonal s)) := by
      ext x; constructor; intro h
      rw [Finset.mem_map]
      use (expPerm σ⁻¹ x.1, expPerm σ⁻¹ x.2); constructor; swap

      rw [hed, expPerm_inv, expPerm_inv]

      rw [Finset.mem_antidiagonal]; rw [Finset.mem_antidiagonal] at h
      simp only
      apply_fun (expPerm σ⁻¹) at h
      rw [← expPerm_add, expPerm_inv'] at h
      exact h


      intro h; rw [Finset.mem_antidiagonal]
      rw [Finset.mem_map] at h
      obtain ⟨a, has, h⟩ := h
      rw [Finset.mem_antidiagonal] at has
      rw [hed] at h
      obtain ⟨h1, h2⟩ := h
      simp only
      apply_fun expPerm σ at has
      rw [expPerm_add]; exact has
    let f : β × β → 𝕜 := fun x => (MvPolynomial.coeff x.1 p)*(MvPolynomial.coeff x.2 q)
    have hfd : ∀ x : β × β, f x = (MvPolynomial.coeff x.1 p)*(MvPolynomial.coeff x.2 q) := by intro x; rfl
    have hfe : ∀ x : β × β, f (e x) = (MvPolynomial.coeff (expPerm σ x.1) p)*(MvPolynomial.coeff (expPerm σ x.2) q) := by
      intro x; rfl
    simp only [hes, ← hfd, ← hfe]
    apply Finset.sum_map (Finset.antidiagonal s) e f

noncomputable instance instEquivLike : EquivLike (permActs α 𝕜) (MvPolynomial α 𝕜) (MvPolynomial α 𝕜) where
  coe := instFunLike.coe
  inv := fun σ => ((σ : Equiv.Perm α)⁻¹ : permActs α 𝕜)
  left_inv := by
    intro σ;simp only
    refine Function.leftInverse_iff_comp.mpr ?_
    ext p s; simp only [Function.comp_apply, id_eq, DFunLike.coe]
    rw [act_coeff, act_coeff, expPerm_inv]
  right_inv := by
    intro σ; simp only
    apply Function.rightInverse_iff_comp.mpr ?_
    ext p s; simp only [Function.comp_apply, id_eq, DFunLike.coe]
    rw [act_coeff, act_coeff, expPerm_inv']
  coe_injective' := by
    intro σ τ hst hact
    simp only [DFunLike.coe_fn_eq, inv_inj] at hact; exact hact
instance instRingEquivClass : RingEquivClass (permActs α 𝕜) (MvPolynomial α 𝕜) (MvPolynomial α 𝕜) where
  map_mul := by
    intro σ p q
    apply SymmetricAction.smul_mul
  map_add := instAddHom.map_add

noncomputable def IsSymmetric (I : Ideal (MvPolynomial α 𝕜)) :=
  ∀ σ : (Equiv.Perm α), ∀ f ∈ I, σ • f ∈ I

lemma is_symm_iff_stable_image {I : Ideal (MvPolynomial α 𝕜)} : IsSymmetric I ↔ ∀ σ : (permActs α 𝕜),
  Ideal.map σ I = I := by
    constructor; intro h σ
    ext f; constructor; intro hi
    apply (Ideal.mem_map_of_equiv σ f).mp at hi
    obtain ⟨g, hi, hg⟩ := hi
    rw [← hg]
    apply h σ g hi

    intro hi
    have hfσ : σ (σ⁻¹ • f) = f := by
      have hasd : σ (σ⁻¹ • f) = σ • (σ⁻¹ • f) := by rfl
      rw [hasd]
      exact smul_inv_smul σ f
    rw [← hfσ]
    apply Ideal.mem_map_of_mem
    exact h σ⁻¹ f hi

    intro h σ f hi
    specialize h σ
    have hf : σ • f = (instFunLike.coe σ) f := by rfl
    rw [← h, hf]
    apply Ideal.mem_map_of_mem; exact hi

def symmSet (S : Set (MvPolynomial α 𝕜)) : Set (MvPolynomial α 𝕜) := ⋃ σ : (Equiv.Perm α), ((σ • .) '' S)
def symmSpan (S : Set (MvPolynomial α 𝕜)) : Ideal (MvPolynomial α 𝕜) := Ideal.span (symmSet S)

lemma symmSet_is_symm {S : Set (MvPolynomial α 𝕜)} {σ : (permActs α 𝕜)} : σ '' (symmSet S) = symmSet S := by
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
  use σ⁻¹ f; constructor; swap; apply EquivLike.apply_inv_apply
  unfold symmSet at h; unfold symmSet
  rw [Set.mem_iUnion] at h; rw [Set.mem_iUnion]
  obtain ⟨τ, h⟩ := h; use σ⁻¹ * τ
  rw [Set.mem_image] at h; rw [Set.mem_image]
  obtain ⟨g, hs, hg⟩ := h; use g
  constructor; exact hs
  rw [mul_smul, hg]
  rfl

lemma symmSpan_is_symm {S : Set (MvPolynomial α 𝕜)} : IsSymmetric (symmSpan S) := by
  apply is_symm_iff_stable_image.mpr
  intro σ; unfold symmSpan
  rw [Ideal.map_span, symmSet_is_symm]

noncomputable def IsPrincipalSymmetric (I : Ideal (MvPolynomial α 𝕜)) := ∃ f : MvPolynomial α 𝕜,
  I = symmSpan {f}

lemma psi_is_symm {I : Ideal (MvPolynomial α 𝕜)} : IsPrincipalSymmetric I → IsSymmetric I := by
  intro h
  obtain ⟨f, h⟩ := h
  rw [h]
  exact symmSpan_is_symm



open Classical
lemma psi_mgs_factorial {I : Ideal (MvPolynomial α 𝕜)} : IsPrincipalSymmetric I →
  (μ (MvPolynomial α 𝕜) I ≤ (α.card).factorial) := by
    intro h; obtain ⟨f, h⟩ := h
    let S' := symmSet {f}
    let F : MvPolynomial α 𝕜 → Equiv.Perm α := fun g => if hg : ∃ σ : Equiv.Perm α, g = σ • f then Classical.choose hg else 1
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

    have han : n ≤ α.card.factorial := by
      unfold n
      rw [← Fintype.card_coe α, ← Fintype.card_perm, Set.toFinset_card S']
      apply Set.InjOn.injective at hsi
      apply Fintype.card_le_of_injective (S'.restrict F) hsi
    apply le_trans ?_ han
    apply Nat.sInf_le
    rw [Set.mem_setOf]
    use S; constructor; rfl
    rw [h]; unfold symmSpan; congr
    simp only [Set.coe_toFinset, S, S']
