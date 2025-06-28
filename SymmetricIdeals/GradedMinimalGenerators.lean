import Mathlib
import SymmetricIdeals.MinDeg
import SymmetricIdeals.SingleDegGen
import SymmetricIdeals.MinimalGenerating


open MvPolynomial

variable {α F : Type*} [Field F]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I : Ideal (MvPolynomial α F)}


variable [Finite α]


lemma homoSubI_mod_fin (n : ℕ) (I : Ideal (MvPolynomial α F)) : Module.Finite F (homogeneousSubmoduleI n I) := by
  suffices Module.Finite F (homogeneousSubmodule α F n) by
    apply Submodule.finiteDimensional_inf_left (homogeneousSubmodule α F n) (Submodule.restrictScalars F I)
  rw [homogeneousSubmodule_eq_finsupp_supported]
  suffices Finite {d : α →₀ ℕ | d.degree = n} by
    apply Module.Finite.of_basis (basisRestrictSupport F {d | d.degree = n})
  have hfbdd : Finite {d : α →₀ ℕ | ∀ a, d a ≤ n} :=
    ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype
  apply Finite.Set.subset {d : α →₀ ℕ | ∀ a, d a ≤ n}
  intro d hd; rw [Set.mem_setOf] at hd
  rw [Set.mem_setOf]; intro a
  rw [← hd]
  exact Finsupp.le_degree a d

lemma homoSubI_mod_fin' (n : ℕ) (I : Ideal (MvPolynomial α F)) : Module.Finite F (Submodule.span F ((homogeneousSubmoduleI n I) : Set (MvPolynomial α F))) := by
  rw [Submodule.span_eq]
  exact homoSubI_mod_fin n I

lemma finrank_mem_minDeg (h : IsSingleDegGen I) : Module.finrank F (homogeneousSubmoduleI (minDeg I) I)
  ∈ {n : ℕ | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S} := by
    rw [Set.mem_setOf]
    have hvsf := homoSubI_mod_fin' (minDeg I) I
    obtain ⟨S, hsub, hcard, hspan, hlid⟩ := Submodule.exists_finset_span_eq_linearIndepOn F ((homogeneousSubmoduleI (minDeg I) I) : Set (MvPolynomial α F))
    use S; constructor;
    apply LinearIndepOn.zero_notMem_image at hlid
    simp only [id_eq, Set.image_id', Finset.mem_coe] at hlid
    exact hlid

    constructor
    rw [hcard]
    rw [Submodule.span_eq]

    rw [h]; apply Submodule.span_eq_span
    rw [← Submodule.span_eq (homogeneousSubmoduleI (minDeg I) I), ← hspan]
    apply Submodule.span_subset_span

    apply subset_trans hsub
    exact Submodule.subset_span

theorem mgs_le_rank (h : IsSingleDegGen I) : min_gen_size I ≤ Module.finrank F (homogeneousSubmoduleI (minDeg I) I) := by
  apply Nat.sInf_le (finrank_mem_minDeg h)



variable [DecidableEq α]

open Classical

omit [Finite α] in lemma finrank_hom_top : Module.finrank F (homogeneousSubmoduleI (minDeg (⊤ : Ideal (MvPolynomial α F))) (⊤ : Ideal (MvPolynomial α F))) = 1 := by
  rw [minDeg_top, ← Ideal.span_singleton_one, homoSubI_span 0 {1}]
  apply finrank_span_singleton
  exact Ne.symm (zero_ne_one' (MvPolynomial α F))
  simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule]
  exact isHomogeneous_one α F

theorem mgs_ge_rank (h : IsSingleDegGen I) : min_gen_size I ≥ Module.finrank F (homogeneousSubmoduleI (minDeg I) I) := by
  by_cases hIT : I = ⊤
  rw [hIT, mgs_top, finrank_hom_top]

  by_cases hmindeg : minDeg I = 0
  let hI0 := zero_of_minDeg_zero (single_deg_gen_homo h) hIT hmindeg
  rw [Submodule.zero_eq_bot] at hI0
  rw [hmindeg, hI0, mgs_bot, ← Submodule.zero_eq_bot, homoSubI_zero]
  simp only [Submodule.zero_eq_bot, finrank_bot, ge_iff_le, le_refl]


  have hmgs : min_gen_size I ∈ { n : ℕ | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S } := by
    apply Nat.sInf_mem
    use Module.finrank F (homogeneousSubmoduleI (minDeg I) I)
    exact finrank_mem_minDeg h
  rw [Set.mem_setOf] at hmgs
  obtain ⟨S, hsz, hcard, hspan⟩ := hmgs
  rw [← hcard, ge_iff_le]
  have hfin : Fintype ((homogeneousComponent (minDeg I)) '' S.toSet) := by apply Fintype.ofFinite
  let S' := ((homogeneousComponent (minDeg I)) '' S.toSet).toFinset
  have hhcS : ∀ p : S', ∃ q : S, (homogeneousComponent (minDeg I)) q = p.1 := by
      intro p; let hp := p.2
      unfold S' at hp
      simp only [Set.mem_toFinset, Set.mem_image, Finset.mem_coe] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      use ⟨q, hq⟩
  have hSS : S'.card ≤ S.card := by
    let f : S' → S := fun p : S' => Classical.choose (hhcS p)
    suffices Function.Injective f by exact Finset.card_le_card_of_injective this
    intro p q hf
    unfold f at hf
    apply Subtype.coe_inj.mp
    rw [← Classical.choose_spec (hhcS p), ← Classical.choose_spec (hhcS q), hf]
  apply le_trans ?_ hSS
  have hscoe : S'.card = (S'.toSet).toFinset.card := by rw [Finset.toFinset_coe S']
  rw [hscoe]
  suffices Module.finrank F (homogeneousSubmoduleI (minDeg I) I) ≤ Module.finrank F (Submodule.span F S'.toSet) by
    apply le_trans this (finrank_span_le_card (S'.toSet))
  apply Submodule.finrank_mono


  rw [← homoSubI_span (minDeg I)]; swap
  intro p hp
  simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, S'] at hp
  obtain ⟨x, hxS, hp⟩ := hp
  rw [← hp, SetLike.mem_coe,
    mem_homogeneousSubmodule (minDeg I) (homogeneousComponent (minDeg I) x)]
  exact homogeneousComponent_isHomogeneous (minDeg I) x

  simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image, S']
  apply homoComps_gen_singleDegGen_ideal h hspan


theorem mgs_eq_rank (h : IsSingleDegGen I) : min_gen_size I = Module.finrank F (homogeneousSubmoduleI (minDeg I) I) := by
  exact antisymm (mgs_le_rank h) (mgs_ge_rank h)


lemma mgs_le_mgs {I J : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
  (h : minDeg I = minDeg J) : I ≤ J → min_gen_size I ≤ min_gen_size J := by
    intro hIJ
    rw [mgs_eq_rank hI, mgs_eq_rank hJ]
    let hfin := homoSubI_mod_fin (minDeg J) J
    apply Submodule.finrank_mono
    unfold homogeneousSubmoduleI
    apply inf_le_inf
    rw [h]
    exact hIJ

lemma mgs_lt_mgs {I J : Ideal (MvPolynomial α F)} (hI : IsSingleDegGen I) (hJ : IsSingleDegGen J)
  (h : minDeg I = minDeg J) : I < J → min_gen_size I < min_gen_size J := by
    intro hIJ
    rw [mgs_eq_rank hI, mgs_eq_rank hJ]
    let hfin := homoSubI_mod_fin (minDeg J) J
    apply Submodule.finrank_lt_finrank_of_lt
    rw [← h]
    apply homoSubI_strictMono (minDeg I) h (rfl) hI hJ hIJ
