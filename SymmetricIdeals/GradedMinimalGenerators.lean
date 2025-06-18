import Mathlib


open MvPolynomial

variable {F : Type*} [Field F]
variable {α : Type*}

noncomputable
def min_gen_size {R : Type*} [Semiring R] (I : Ideal R) : ℕ
  := sInf { n : ℕ | ∃ S : Finset R, 0 ∉ S ∧ S.card = n ∧ I = Ideal.span ↑S}

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I : Ideal (MvPolynomial α F)}


def homogeneousSubmoduleI (n : ℕ) (I : Ideal (MvPolynomial α F)) : Submodule F (MvPolynomial α F) :=
  (homogeneousSubmodule α F n) ⊓ (Submodule.restrictScalars F I)

lemma eq_of_homo_homoComp {n : ℕ} (p q : MvPolynomial α F) (hqz : q ≠ 0) (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n)
  (h : (homogeneousComponent n) p = (homogeneousComponent n) q) : p = q := by
    rw [← sum_homogeneousComponent p, ← sum_homogeneousComponent q]
    suffices (fun i : ℕ => (homogeneousComponent i) p) = (fun i : ℕ => (homogeneousComponent i) q) by
      congr 3
      rw [IsHomogeneous.totalDegree hp, IsHomogeneous.totalDegree hq hqz]
      apply_fun (homogeneousComponent n)
      rw [← mem_homogeneousSubmodule] at hq
      rw [map_zero, h, homogeneousComponent_of_mem hq]
      simp only [↓reduceIte]; exact hqz
    ext i : 1
    by_cases hin : i = n
    rw [hin]; exact h

    rw [homogeneousComponent_of_mem hp, homogeneousComponent_of_mem hq]
    simp only [hin, ↓reduceIte]

lemma coeff_mul_single_homo [DecidableEq α] {S : Set (MvPolynomial α F)} {d : α →₀ ℕ} {k n : ℕ}
  {f : Fin k → MvPolynomial α F} {g : Fin k → S} (i : Fin k)
  (hd : d.degree = n) (hg : ∀ i, (g i).1.IsHomogeneous n) :
  coeff d ((f i) * (g i).1) = coeff 0 (f i) * coeff d (g i).1 := by
    rw [coeff_mul]
    apply Finset.sum_eq_single_of_mem (0,d)
    rw [Finset.mem_antidiagonal, zero_add]
    intro b hab hbd
    rw [Finset.mem_antidiagonal] at hab
    by_cases hb2 : b.2.degree ≠ n
    suffices coeff b.2 (g i).1 = 0 by rw [this, mul_zero];
    contrapose! hb2
    apply hg at hb2; rw [← hb2]
    simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
      id_eq, smul_eq_mul, mul_one];
    rfl

    push_neg at hb2
    let hab2 := hab
    apply_fun Finsupp.degree at hab2
    rw [Finsupp.degree_add, hb2, hd, Nat.add_eq_right, Finsupp.degree_eq_zero_iff] at hab2
    rw [hab2, zero_add] at hab
    have hb : b = (0, d) := by exact Prod.ext hab2 hab
    have hfalse : False := by exact hbd hb
    contradiction


lemma homoSubI_span [DecidableEq α] (n : ℕ) (S : Set (MvPolynomial α F)) (h : S ⊆ (homogeneousSubmodule α F n)) :
  homogeneousSubmoduleI n (Ideal.span S) = Submodule.span F S := by
    ext p; constructor; intro hp
    by_cases hpz : p = 0
    rw [hpz]; exact Submodule.zero_mem (Submodule.span F S)

    apply Submodule.mem_span_set'.mpr
    obtain ⟨hpm, hp⟩ := Submodule.mem_inf.mp hp
    rw [mem_homogeneousSubmodule] at hpm
    rw [Submodule.restrictScalars_mem] at hp
    apply Submodule.mem_span_set'.mp at hp
    obtain ⟨k, f, g, hp⟩ := hp; use k
    let f' : Fin k → F := fun i => coeff 0 (f i)
    use f'; use g

    have hg : ∀ i, (g i).1.IsHomogeneous n := by
      intro i
      suffices ↑(g i) ∈ (homogeneousSubmodule α F n) by
        rw [← mem_homogeneousSubmodule]
        exact this
      apply h
      exact (g i).2

    simp only [f', smul_eq_C_mul]
    have hsh : (∑ i, C (coeff 0 (f i)) * ((g i) : MvPolynomial α F)).IsHomogeneous n := by
      apply IsHomogeneous.sum; intro i hif
      apply IsHomogeneous.C_mul
      exact hg i
    apply eq_of_homo_homoComp _ _ hpz hsh hpm
    rw [homogeneousComponent_of_mem hsh]; simp only [reduceIte]
    suffices (homogeneousComponent n) (∑ i, (f i) • ((g i) : MvPolynomial α F)) = ∑ i, C (coeff 0 (f i)) * ((g i) : MvPolynomial α F) by
      rw [← this]
      apply_fun (homogeneousComponent n) at hp
      exact hp
    simp only [smul_eq_mul, map_sum]
    congr; ext i d

    rw [homogeneousComponent_apply]
    rw [coeff_sum]
    simp only [coeff_monomial d, Finset.sum_ite_eq', Finset.mem_filter, mem_support_iff, ne_eq, coeff_C_mul]
    by_cases hd : d ∈ (f i * ↑(g i)).support ∧ d.degree = n
    simp only [Finset.mem_filter, hd, and_self, ↓reduceIte]
    apply coeff_mul_single_homo i hd.2 hg

    have hd2 : d ∉ {d ∈ (f i * (g i)).support | d.degree = n} := by apply Finset.mem_filter.not.mpr hd
    simp only [hd2, ↓reduceIte, zero_eq_mul]
    rw [not_and'] at hd; rw [or_iff_not_imp_left]; intro hfi
    by_cases hdn : d.degree ≠ n

    contrapose! hdn
    specialize hg i hdn
    simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
      id_eq, smul_eq_mul, mul_one, Finsupp.sum] at hg
    rw [← hg]; rfl


    push_neg at hdn; specialize hd hdn
    rw [notMem_support_iff] at hd
    suffices coeff d ((f i)*(g i).1) = coeff (0,d).1 (f i) * coeff (0,d).2 (g i).1 by
      simp only at this
      rw [hd] at this; symm at this
      exact (mul_eq_zero_iff_left hfi).mp this
    apply coeff_mul_single_homo i hdn hg



    intro hp; unfold homogeneousSubmoduleI
    apply Submodule.mem_inf.mpr; constructor

    have hsf : Submodule.span F S ≤ Submodule.span F (homogeneousSubmodule α F n) := Submodule.span_monotone h
    apply hsf at hp
    rw [Submodule.span_eq] at hp
    exact hp

    rw [Submodule.restrictScalars_mem, ← Ideal.submodule_span_eq]
    suffices ((Submodule.span F S) : Set (MvPolynomial α F)) ⊆ ↑(Submodule.span (MvPolynomial α F) S) by apply this hp
    apply Submodule.span_subset_span

noncomputable
def minDeg (I : Ideal (MvPolynomial α F)) := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}
noncomputable
def IsSingleDegGen (I : Ideal (MvPolynomial α F)) := I = Ideal.span (homogeneousSubmoduleI (minDeg I) I)

lemma ideal_span_subset_zero_singleton {S : Set (MvPolynomial α F)} (h : S ⊆ {0}) : Ideal.span S = 0 := by
  apply Set.subset_singleton_iff_eq.mp at h
  rcases h with h|h
  rw [h, Ideal.span_empty, Ideal.zero_eq_bot];
  rw [h, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

lemma min_deg_homo [DecidableEq α] {n : ℕ} {S : Set (MvPolynomial α F)} (hS : ∃ p ∈ S, p ≠ 0) (h : S ⊆ homogeneousSubmodule α F n) : minDeg (Ideal.span S) = n := by
  unfold minDeg
  have hn : n ∈ {n | homogeneousSubmoduleI n (Ideal.span S) ≠ ⊥} := by
    rw [Set.mem_setOf]
    rw [homoSubI_span n S h]
    apply Submodule.span_eq_bot.not.mpr; push_neg
    exact hS
  apply antisymm (Nat.sInf_le hn)
  apply le_csInf; use n
  intro m; rw [Set.mem_setOf];
  contrapose!; intro hnm
  rw [Submodule.eq_bot_iff]
  intro p hp; unfold homogeneousSubmoduleI at hp
  rw [Submodule.mem_inf] at hp
  let hpS : p ∈ Ideal.span S := hp.2; apply And.left at hp
  unfold Ideal.span at hpS
  rw [Submodule.mem_span_iff_exists_finset_subset] at hpS
  obtain ⟨f, T, hTS, hfT, hps⟩ := hpS
  by_contra! hpz
  suffices ∀ i ∈ Finset.range (p.totalDegree+1), (homogeneousComponent i p) = 0 by
    rw [← sum_homogeneousComponent p] at hpz
    apply Finset.sum_eq_zero at this
    exact hpz this
  intro i
  rw [mem_homogeneousSubmodule] at hp
  have hptd : p.totalDegree = m := IsHomogeneous.totalDegree hp hpz
  rw [hptd]; intro ir
  rw [Finset.mem_range] at ir
  apply Nat.lt_of_lt_of_le ir at hnm
  simp only [← hps, smul_eq_mul, map_sum]
  suffices ∀ x ∈ T, (homogeneousComponent i) ((f x) * x) = 0 by exact Finset.sum_eq_zero this
  intro x hxT
  rw [mul_def]; simp only [Finsupp.sum, map_sum]
  suffices ∀ x₁ ∈ (f x).support, ∑ x₂ ∈ x.support, (homogeneousComponent i) ((monomial (x₁+x₂)) (((f x).2 x₁) * (x.2 x₂))) = 0 by
    exact Finset.sum_eq_zero this
  intro x₁ hx₁
  suffices ∀ x₂ ∈ x.support, (homogeneousComponent i) ((monomial (x₁+x₂)) (((f x).2 x₁) * (x.2 x₂))) = 0 by
    exact Finset.sum_eq_zero this
  intro x₂ hx₂
  refine homogeneousComponent_eq_zero' i ((monomial (x₁ + x₂)) ((f x).toFun x₁ * x.toFun x₂)) ?_
  intro d hd
  simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff, mul_eq_zero,
    Classical.not_imp, not_or] at hd
  rw [← hd.1]
  apply ne_of_gt
  apply lt_of_lt_of_le hnm
  rw [Finsupp.degree_add]
  suffices x₂.degree = n by
    rw [this]
    exact Nat.le_add_left n x₁.degree
  apply hTS at hxT
  apply h at hxT
  rw [SetLike.mem_coe, mem_homogeneousSubmodule] at hxT
  rw [mem_support_iff] at hx₂
  specialize hxT hx₂
  rw [← hxT]
  unfold Finsupp.degree Finsupp.weight Finsupp.linearCombination Finsupp.support
  simp only [Pi.one_apply, LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
  rfl

lemma homogeneousSubmoduleI_zero : homogeneousSubmoduleI 0 (0 : Ideal (MvPolynomial α F)) = 0 := by
  simp only [homogeneousSubmoduleI, Submodule.zero_eq_bot, Submodule.restrictScalars_bot, bot_le,
    inf_of_le_right]
lemma homogeneousSubmoduleI_n_zero {n : ℕ} : homogeneousSubmoduleI n (0 : Ideal (MvPolynomial α F)) = 0 := by
  simp only [homogeneousSubmoduleI, Submodule.zero_eq_bot, Submodule.restrictScalars_bot, bot_le,
    inf_of_le_right]

lemma min_deg_bot : minDeg (⊥ : Ideal (MvPolynomial α F)) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  right; apply Set.subset_empty_iff.mp
  intro n hn; rw [Set.mem_setOf] at hn
  specialize hn homogeneousSubmoduleI_n_zero
  contradiction

lemma zero_singleDegGen : IsSingleDegGen (0 : Ideal (MvPolynomial α F)) := by
  unfold IsSingleDegGen
  rw [homogeneousSubmoduleI_n_zero]
  exact Eq.symm (ideal_span_subset_zero_singleton fun ⦃a⦄ ↦ congrArg fun ⦃a⦄ ↦ a)

theorem singleDegGen_iff [DecidableEq α] : IsSingleDegGen I ↔ ∃ n : ℕ, ∃ S : Set (MvPolynomial α F), S ⊆ (homogeneousSubmodule α F n) ∧ I = Ideal.span S := by
  constructor; intro h
  use (minDeg I); use (homogeneousSubmoduleI (minDeg I) I); constructor
  apply inf_le_left
  exact h

  intro h
  obtain ⟨n, S, hS, hspan⟩ := h
  by_cases hzS : ∃ p ∈ S, p ≠ 0
  unfold IsSingleDegGen
  nth_rw 1 [hspan]; nth_rw 1 [hspan, min_deg_homo hzS hS]
  apply Submodule.span_eq_span

  apply le_trans ?_ Submodule.subset_span
  apply le_inf hS
  intro s hs; rw [Submodule.coe_restrictScalars, SetLike.mem_coe, hspan]
  apply (Ideal.subset_span) hs

  apply le_trans (inf_le_right)
  simp only [Submodule.coe_restrictScalars, Ideal.submodule_span_eq, Set.le_eq_subset,
    SetLike.coe_subset_coe]
  rw [hspan]


  push_neg at hzS
  have hSz : S ⊆ {0} := by exact hzS
  apply ideal_span_subset_zero_singleton at hSz
  rw [hspan, hSz]
  exact zero_singleDegGen

--theorem singleDegGen_iff' : IsSingleDegGen I ↔ ∃ S : Set (MvPolynomial α F), S ⊆ (homogeneousSubmodule α F (minDeg I) ) ∧ I = Ideal.span S := by sorry

theorem single_deg_gen_homo (h : IsSingleDegGen I) : Ideal.IsHomogeneous (homogeneousSubmodule α F) I := by
  apply (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule α F) I).mpr
  let n := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}
  let S := homogeneousSubmoduleI n I
  have hS : ∀ s ∈ S, s ∈ (SetLike.homogeneousSubmonoid (homogeneousSubmodule α F)) := by
    intro s hs; unfold S at hs
    apply Submonoid.mem_carrier.mp
    simp only [SetLike.homogeneousSubmonoid, Set.mem_setOf]
    apply Submodule.mem_inf.mp at hs; apply And.left at hs
    unfold SetLike.IsHomogeneousElem; use n
  let fs : S → (SetLike.homogeneousSubmonoid (homogeneousSubmodule α F)) := fun s => ⟨s, by exact hS s.1 s.2⟩
  use Set.range fs; rw [h]; congr

  ext p; constructor; intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right]
  rw [SetLike.mem_coe] at h
  use (hS p h); use p; use h

  intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right] at h
  rw [SetLike.mem_coe]
  obtain ⟨_, q, hp, hpq⟩ := h
  apply Subtype.mk_eq_mk.mp at hpq
  simp only at hpq
  rw [hpq] at hp
  exact hp

lemma homogeneousSubmoduleI_monotone (n : ℕ) {I J : Ideal (MvPolynomial α F)} : I ≤ J
  → homogeneousSubmoduleI n I ≤ homogeneousSubmoduleI n J := by
    intro hij
    apply inf_le_inf_left
    exact hij

lemma mgs_zero : min_gen_size (0 : Ideal (MvPolynomial α F)) = 0 := by
  unfold min_gen_size
  suffices 0 ∈ {n | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ (0 : Ideal (MvPolynomial α F)) = Ideal.span S} by
    apply Nat.sInf_eq_zero.mpr; left; exact this
  rw [Set.mem_setOf]; use ∅
  constructor; exact Finset.notMem_empty 0; constructor
  rfl; symm
  simp only [Finset.coe_empty, Ideal.span_empty, Submodule.zero_eq_bot]

lemma min_deg_mem (h : minDeg I ≠ 0) : minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  apply Nat.sInf_mem
  contrapose! h
  unfold minDeg; rw [h]
  apply Nat.sInf_empty

lemma min_deg_top : minDeg (⊤ : Ideal (MvPolynomial α F)) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left; rw [Set.mem_setOf]
  apply (Submodule.ne_bot_iff (homogeneousSubmodule α F 0 ⊓ Submodule.restrictScalars F ⊤)).mpr
  use 1; constructor; swap; exact Ne.symm (zero_ne_one' (MvPolynomial α F))
  apply Submodule.mem_inf.mpr; constructor
  rw [mem_homogeneousSubmodule]; exact isHomogeneous_one α F
  simp only [Submodule.restrictScalars_top, Submodule.mem_top]

lemma zero_mem_min_deg : 0 ∈ {n | homogeneousSubmoduleI n I ≠ ⊥} → I = ⊤ := by
  intro hIT
  rw [Set.mem_setOf] at hIT
  apply (Submodule.ne_bot_iff (homogeneousSubmoduleI 0 I)).mp at hIT
  obtain ⟨p, hps, hpz⟩ := hIT
  apply Submodule.mem_inf.mp at hps
  rw [mem_homogeneousSubmodule, Submodule.restrictScalars_mem] at hps
  obtain ⟨hph, hpI⟩  := hps
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hph
  apply Ideal.eq_top_of_isUnit_mem I hpI
  rw [hph]; apply IsUnit.map C
  apply Ne.isUnit
  contrapose! hpz
  rw [hpz, C_0] at hph
  exact hph

lemma empty_min_deg (h : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) :
  {n | homogeneousSubmoduleI n I ≠ ⊥} = ∅ → I = ⊥ := by
    intro hIB
    apply (Submodule.eq_bot_iff I).mpr
    intro p hpI
    rw [← sum_homogeneousComponent p]
    suffices ∀ i : ℕ, homogeneousComponent i p = 0 by simp only [this, Finset.sum_const_zero]
    intro i
    have hiI : homogeneousSubmoduleI i I = ⊥ := by contrapose! hIB; use i; rw [Set.mem_setOf]; exact hIB
    suffices homogeneousComponent i p ∈ homogeneousSubmoduleI i I by rw [hiI] at this; exact this
    unfold homogeneousSubmoduleI; rw [Submodule.mem_inf]; constructor
    exact homogeneousComponent_mem i p
    rw [Submodule.restrictScalars_mem]
    specialize h i hpI
    have hd : (DirectSum.decompose (homogeneousSubmodule α F)) p = DirectSum.Decomposition.decompose' p := by rfl
    rw [hd, decomposition.decompose'_apply] at h
    exact h

lemma min_deg_zero_iff (h : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) :
  minDeg I = 0 ↔ I = ⊤ ∨ I = ⊥ := by
    constructor; swap; intro hI
    rcases hI with hIT|hIB
    rw [hIT]; exact min_deg_top
    rw [hIB]; exact min_deg_bot

    intro hI
    apply Nat.sInf_eq_zero.mp at hI
    rcases hI with hIT|hIB
    left; exact zero_mem_min_deg hIT
    right; exact empty_min_deg h hIB


lemma min_deg_zero (hh : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) (hIT : I ≠ ⊤) :
  minDeg I = 0 → I = 0 := by
    intro hI
    apply Nat.sInf_eq_zero.mp at hI
    let hIT := hIT ∘ zero_mem_min_deg
    rw [imp_false] at hIT
    simp only [hIT, false_or] at hI
    exact empty_min_deg hh hI

lemma min_deg_exists (h : minDeg I ≠ 0) : ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  apply min_deg_mem at h
  rw [Set.mem_setOf] at h
  apply Submodule.exists_mem_ne_zero_of_ne_bot at h
  obtain ⟨p, h⟩ := h
  use p; constructor
  exact (Submodule.mem_inf.mp h.1).2
  constructor; exact h.2
  apply And.left at h;
  apply Submodule.mem_inf.mp at h
  exact (mem_homogeneousSubmodule (minDeg I) p).mp h.1

lemma finrank_hom_top [DecidableEq α] : Module.finrank F (homogeneousSubmoduleI (minDeg (⊤ : Ideal (MvPolynomial α F))) (⊤ : Ideal (MvPolynomial α F))) = 1 := by
  rw [min_deg_top, ← Ideal.span_singleton_one, homoSubI_span 0 {1}]
  apply finrank_span_singleton
  exact Ne.symm (zero_ne_one' (MvPolynomial α F))
  simp only [Set.singleton_subset_iff, SetLike.mem_coe, mem_homogeneousSubmodule]
  exact isHomogeneous_one α F


variable [Finite α]

lemma min_deg_fin_gen (I : Ideal (MvPolynomial α F)) : Module.Finite F (Submodule.span F ((homogeneousSubmoduleI (minDeg I) I) : Set (MvPolynomial α F))) := by
  rw [Submodule.span_eq]
  suffices Module.Finite F (homogeneousSubmodule α F (minDeg I)) by
    apply Submodule.finiteDimensional_inf_left (homogeneousSubmodule α F (minDeg I)) (Submodule.restrictScalars F I)
  rw [homogeneousSubmodule_eq_finsupp_supported]
  suffices Finite {d : α →₀ ℕ | d.degree = minDeg I} by
    apply Module.Finite.of_basis (basisRestrictSupport F {d | d.degree = minDeg I})
  have hfbdd : Finite {d : α →₀ ℕ | ∀ a, d a ≤ minDeg I} :=
    ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype
  apply Finite.Set.subset {d : α →₀ ℕ | ∀ a, d a ≤ minDeg I}
  intro d hd; rw [Set.mem_setOf] at hd
  rw [Set.mem_setOf]; intro a
  rw [← hd]
  exact Finsupp.le_degree a d

lemma finrank_in_span_card (h : IsSingleDegGen I) : Module.finrank F (homogeneousSubmoduleI (minDeg I) I)
  ∈ {n : ℕ | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S} := by
    rw [Set.mem_setOf]
    have hvsf := min_deg_fin_gen I
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
  apply Nat.sInf_le (finrank_in_span_card h)

lemma mgs_pos (h : I ≠ ⊥) : min_gen_size I > 0 := by
  apply Nat.pos_iff_ne_zero.mpr
  unfold min_gen_size
  apply Nat.sInf_eq_zero.not.mpr
  simp only [Set.mem_setOf_eq, Finset.card_eq_zero, existsAndEq, Finset.notMem_empty,
    not_false_eq_true, Finset.coe_empty, Ideal.span_empty, true_and, not_or, ne_eq]
  constructor; exact h
  obtain ⟨S, hspan⟩ := ((isNoetherianRing_iff_ideal_fg (MvPolynomial α F)).mp isNoetherianRing) I
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

lemma mgs_top : min_gen_size (⊤ : Ideal (MvPolynomial α F)) = 1 := by
  have hle : min_gen_size (⊤ : Ideal (MvPolynomial α F)) ≥ 1 := mgs_pos (Ne.symm bot_ne_top)
  apply antisymm hle
  apply Nat.sInf_le; rw [Set.mem_setOf]
  use {1}; constructor; simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true]
  constructor; rfl
  simp only [Finset.coe_singleton, Ideal.span_singleton_one]

omit [Finite α] in lemma homoSubI_iSup {n : ℕ} {f : ℕ → Ideal (MvPolynomial α F)}
  (hh : ∀ i, (f i).IsHomogeneous (homogeneousSubmodule α F)) :
  homogeneousSubmoduleI n (⨆ i, f i) = ⨆ i, (homogeneousSubmoduleI n (f i)) := by
    let g : ℕ → Submodule F (MvPolynomial α F) := fun i => (homogeneousSubmoduleI n (f i))
    ext p; constructor; intro hp
    unfold homogeneousSubmoduleI at hp
    rw [Submodule.mem_inf] at hp

    apply (Submodule.mem_iSup g).mpr
    intro N hN
    let hph := hp.1; let hps := hp.2
    rw [Submodule.restrictScalars_mem] at hps
    let f' : ℕ → Submodule F (MvPolynomial α F) := fun i => Submodule.restrictScalars F (f i)
    have hps' : p ∈ ⨆ i, f' i := by
      rw [Submodule.mem_iSup_iff_exists_finsupp] at hps
      obtain ⟨a, haf, has⟩ := hps
      rw [Submodule.mem_iSup_iff_exists_finsupp]
      use a; constructor; swap; exact has
      intro i; specialize haf i
      unfold f'; rw [Submodule.restrictScalars_mem]
      exact haf
    rw [Submodule.mem_iSup_iff_exists_finsupp] at hps'
    obtain ⟨a, hf, hpf⟩ := hps'
    apply_fun (homogeneousComponent n) at hpf
    rw [homogeneousComponent_of_mem hp.1] at hpf
    simp only [↓reduceIte] at hpf
    rw [← hpf]
    simp only [Finsupp.sum, map_sum]

    suffices ∀ x ∈ a.support, homogeneousComponent n (a x) ∈ N by exact Submodule.sum_mem N this
    intro x hx
    specialize hf x; specialize hN x; specialize hh x
    apply hN; unfold g homogeneousSubmoduleI
    rw [Submodule.mem_inf]; constructor
    exact homogeneousComponent_mem n (a x)
    suffices (a x) ∈ Submodule.restrictScalars F (f x) by
      specialize hh n this
      rw [Submodule.restrictScalars_mem]
      suffices DirectSum.decompose (homogeneousSubmodule α F) (a x) n = (homogeneousComponent n) (a x) by
        rw [this] at hh
        exact hh
      apply decompose'_apply
    exact hf

    intro hp
    apply (Submodule.mem_iSup g).mp at hp
    rw [homogeneousSubmoduleI, Submodule.mem_inf]; constructor
    apply hp (homogeneousSubmodule α F n)
    intro i; unfold g homogeneousSubmoduleI
    exact inf_le_left
    apply hp (Submodule.restrictScalars F (⨆ i, f i))
    intro i; unfold g homogeneousSubmoduleI
    apply le_trans (inf_le_right)
    suffices f i ≤ ⨆ i, f i by
      exact this
    intro q hq
    exact Submodule.mem_iSup_of_mem i hq


variable [DecidableEq α]

omit [Finite α] in lemma homoSubI_span_apply {n m : ℕ} {S : Set (MvPolynomial α F)} (hnm : m ≥ n) (h : S ⊆ homogeneousSubmodule α F m) :
  homogeneousSubmoduleI n (Ideal.span S) = if n = m then homogeneousSubmoduleI m (Ideal.span S) else 0 := by
    by_cases heq : n = m
    rw [heq]; simp only [reduceIte]

    simp only [heq, reduceIte]
    apply (Submodule.eq_bot_iff (homogeneousSubmoduleI n (Ideal.span S))).mpr
    intro p hp
    by_cases hS : ∃ p ∈ S, p ≠ 0

    apply lt_of_le_of_ne hnm at heq
    apply min_deg_homo hS at h
    rw [← h] at heq
    apply Nat.notMem_of_lt_sInf at heq
    rw [Set.mem_setOf] at heq; push_neg at heq
    rw [heq] at hp
    exact hp

    push_neg at hS
    apply Ideal.span_eq_bot.mpr at hS
    rw [hS, ← Submodule.zero_eq_bot, homogeneousSubmoduleI_n_zero] at hp
    exact hp

omit [Finite α] in theorem homoSubI_span_eq {n : ℕ} {S : Set (MvPolynomial α F)} {f : ℕ → Set (MvPolynomial α F)}
  (hS : S = f n) (hf : ∀ i ≥ n, f i ⊆ homogeneousSubmodule α F i) (hfz : ∀ i < n, f i ⊆ {0}) :
  homogeneousSubmoduleI n (Ideal.span S) = homogeneousSubmoduleI n (Ideal.span (⋃ i, f i)) := by
    rw [Ideal.span_iUnion, homoSubI_iSup]; swap
    intro i
    by_cases hin : i < n
    let hI0 := ideal_span_subset_zero_singleton (hfz i hin)
    rw [hI0]
    apply Ideal.IsHomogeneous.bot

    push_neg at hin
    specialize hf i hin
    suffices IsSingleDegGen (Ideal.span (f i)) by exact single_deg_gen_homo this
    apply singleDegGen_iff.mpr; use i; use f i

    have hss : ∀ i, homogeneousSubmoduleI n (Ideal.span (f i)) = if n = i then homogeneousSubmoduleI i (Ideal.span (f i)) else 0 := by
      intro i
      by_cases hin : i ≥ n
      exact homoSubI_span_apply hin (hf i hin)
      push_neg at hin
      suffices Ideal.span (f i) = 0 by
        rw [this]
        let hn := Nat.ne_of_lt' hin
        simp only [hn, ↓reduceIte]
        exact homogeneousSubmoduleI_n_zero
      exact ideal_span_subset_zero_singleton (hfz i hin)

    simp only [hss, Submodule.zero_eq_bot]
    rw [iSup_ite]
    simp only [iSup_iSup_eq_right, iSup_bot, bot_le, sup_of_le_left]
    rw [hS]


open Classical

theorem mgs_ge_rank (h : IsSingleDegGen I) : min_gen_size I ≥ Module.finrank F (homogeneousSubmoduleI (minDeg I) I) := by
  by_cases hIT : I = ⊤
  rw [hIT, mgs_top, finrank_hom_top]

  by_cases hmindeg : minDeg I = 0
  let hI0 := min_deg_zero (single_deg_gen_homo h) hIT hmindeg
  rw [hmindeg, hI0]
  rw [mgs_zero, homogeneousSubmoduleI_zero]
  simp only [Submodule.zero_eq_bot, finrank_bot, ge_iff_le, le_refl]


  have hmgs : min_gen_size I ∈ { n : ℕ | ∃ S : Finset (MvPolynomial α F), 0 ∉ S ∧ S.card = n ∧ I = Ideal.span S } := by
    apply Nat.sInf_mem
    use Module.finrank F (homogeneousSubmoduleI (minDeg I) I)
    exact finrank_in_span_card h
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

  let Sa := ⋃ i : ℕ, (homogeneousComponent i) '' S.toSet
  have hsas : homogeneousSubmoduleI (minDeg I) (Ideal.span S') = homogeneousSubmoduleI (minDeg I) (Ideal.span Sa) := by
    apply homoSubI_span_eq
    ext p; constructor; intro hpS
    simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, S'] at hpS
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Sa]
    exact hpS

    intro hpS
    simp only [Set.toFinset_image, Finset.toFinset_coe, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, S']
    simp only [Set.mem_image, Finset.mem_coe, S'] at hpS
    exact hpS

    intro i hi p hp
    simp only [Set.mem_image, Finset.mem_coe] at hp
    simp only [SetLike.mem_coe, mem_homogeneousSubmodule]
    obtain ⟨q, hqS, hq⟩ := hp
    rw [← hq]
    exact homogeneousComponent_isHomogeneous i q

    intro i hi p hp
    simp only [Set.mem_image, Finset.mem_coe, S'] at hp
    obtain ⟨q, hqS, hq⟩ := hp
    rw [Set.mem_singleton_iff]
    apply Nat.notMem_of_lt_sInf at hi; rw [Set.mem_setOf] at hi; push_neg at hi
    suffices p ∈ homogeneousSubmoduleI i I by
      rw [hi] at this
      exact this
    unfold homogeneousSubmoduleI
    rw [← hq, Submodule.mem_inf]; constructor
    exact homogeneousComponent_mem i q
    rw [Submodule.restrictScalars_mem]
    apply single_deg_gen_homo at h
    suffices q ∈ I by
      specialize h i this
      have hd : (DirectSum.decompose (homogeneousSubmodule α F)) q = DirectSum.Decomposition.decompose' q := by rfl
      rw [hd, decomposition.decompose'_apply] at h
      exact h
    rw [hspan]
    apply Submodule.subset_span; exact hqS

  rw [hsas]
  suffices I ≤ Ideal.span Sa by apply homogeneousSubmoduleI_monotone (minDeg I) this

  rw [hspan]
  apply Submodule.span_le.mpr
  intro p hp
  apply Submodule.mem_span_set.mpr
  have hps := sum_homogeneousComponent p
  have hhcp : Fintype (Set.range (homogeneousComponent . p)) := by
    let f : Finset.range (p.totalDegree + 2) → (Set.range (homogeneousComponent . p)) := fun i =>
      ⟨homogeneousComponent i p, by rw [Set.mem_range]; use i⟩
    apply Fintype.ofSurjective f
    intro q; let hq := q.2
    rw [Set.mem_range] at hq
    obtain ⟨i, hq⟩ := hq

    by_cases hi : i ∈ Finset.range (p.totalDegree + 2)
    use ⟨i, hi⟩; unfold f;
    apply Subtype.mk_eq_mk.mpr; rw [Subtype.coe_mk]
    exact hq

    use ⟨p.totalDegree+1, by
      apply Finset.mem_range.mpr
      exact Nat.lt_add_one (p.totalDegree + 1)⟩
    unfold f; apply Subtype.mk_eq_mk.mpr; rw [Subtype.coe_mk]
    rw [homogeneousComponent_eq_zero]
    rw [← hq]; symm
    apply homogeneousComponent_eq_zero
    apply Finset.mem_range.not.mp at hi; push_neg at hi
    apply lt_of_lt_of_le ?_ hi
    exact Nat.lt_add_of_pos_right (zero_lt_two)
    exact lt_add_one p.totalDegree
  let c : MvPolynomial α F →₀ MvPolynomial α F := ⟨(Set.range (homogeneousComponent . p)).toFinset,
    fun q => if q ∈ Set.range (homogeneousComponent . p) then 1 else 0, by
      simp only [Set.mem_toFinset, Set.mem_range, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        not_exists, not_forall, Decidable.not_not, implies_true, S']
    ⟩
  use c; constructor
  simp only [Set.coe_toFinset, c]
  intro q hq
  rw [Set.mem_range] at hq
  obtain ⟨i, hq⟩ := hq; unfold Sa
  rw [← hq, Set.mem_iUnion]
  use i; rw [Set.mem_image]; use p

  unfold Finsupp.sum; rw [← hps]; symm
  let e : (i : ℕ) → (i ∈ Finset.range (p.totalDegree +1)) → ((homogeneousComponent . p) i ≠ 0) → MvPolynomial α F :=
    fun i hi hcz => (homogeneousComponent i) p
  apply Finset.sum_bij_ne_zero e

  intro i h₁ h₂
  simp only [Set.mem_toFinset, Set.mem_range, c, e]; use i

  intro i h₁₁ h₁₂ j h₂₁ h₂₂ he
  unfold e at he
  have hi : ((homogeneousComponent i) p).IsHomogeneous i := by exact homogeneousComponent_isHomogeneous i p
  have hj : ((homogeneousComponent j) p).IsHomogeneous j := by exact homogeneousComponent_isHomogeneous j p
  rw [he] at hi
  apply IsHomogeneous.inj_right hi hj h₂₂

  intro b hb hbz
  simp only [smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hbz
  have hcb : c b ≠ 0 := by exact Finsupp.mem_support_iff.mp hb
  simp only [hcb, not_false_eq_true, true_and] at hbz
  simp only [Set.mem_toFinset, Set.mem_range, c] at hb
  obtain ⟨i, hb⟩ := hb; use i
  rw [← hb] at hbz
  have hifr : i ∈ Finset.range (p.totalDegree + 1) := by
    contrapose! hbz
    apply homogeneousComponent_eq_zero
    rw [Finset.mem_range.not] at hbz; push_neg at hbz
    exact hbz
  use hifr; use hbz

  intro i h₁ h₂
  simp [smul_eq_mul, c, e, S']

omit [DecidableEq α] in theorem mgs_eq_rank [DecidableEq α] (h : IsSingleDegGen I) : min_gen_size I = Module.finrank F (homogeneousSubmoduleI (minDeg I) I) := by
  exact antisymm (mgs_le_rank h) (mgs_ge_rank h)
