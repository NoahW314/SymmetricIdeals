import Mathlib

open MvPolynomial

variable {α F : Type*} [Field F]
variable {I : Ideal (MvPolynomial α F)}

attribute [local instance] MvPolynomial.gradedAlgebra



def homogeneousSubmoduleI (n : ℕ) (I : Ideal (MvPolynomial α F)) : Submodule F (MvPolynomial α F) :=
  (homogeneousSubmodule α F n) ⊓ (Submodule.restrictScalars F I)

lemma homoSubI_monotone (n : ℕ) {I J : Ideal (MvPolynomial α F)} : I ≤ J
  → homogeneousSubmoduleI n I ≤ homogeneousSubmoduleI n J := by
    intro hij
    apply inf_le_inf_left
    exact hij

@[simp] lemma homoSubI_zero {n : ℕ} : homogeneousSubmoduleI n (0 : Ideal (MvPolynomial α F)) = 0 := by
  simp only [homogeneousSubmoduleI, Submodule.zero_eq_bot, Submodule.restrictScalars_bot, bot_le,
    inf_of_le_right]

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

@[simp] theorem homoSubI_span [DecidableEq α] (n : ℕ) (S : Set (MvPolynomial α F)) (h : S ⊆ (homogeneousSubmodule α F n)) :
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

lemma homoSubI_iSup {X : Type*} {n : ℕ} {f : X → Ideal (MvPolynomial α F)} (hh : ∀ i, (f i).IsHomogeneous (homogeneousSubmodule α F)) :
  homogeneousSubmoduleI n (⨆ i, f i) = ⨆ i, (homogeneousSubmoduleI n (f i)) := by
    let g : X → Submodule F (MvPolynomial α F) := fun i => (homogeneousSubmoduleI n (f i))
    ext p; constructor; intro hp
    unfold homogeneousSubmoduleI at hp
    rw [Submodule.mem_inf] at hp

    apply (Submodule.mem_iSup g).mpr
    intro N hN
    let hph := hp.1; let hps := hp.2
    rw [Submodule.restrictScalars_mem] at hps
    let f' : X → Submodule F (MvPolynomial α F) := fun i => Submodule.restrictScalars F (f i)
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



noncomputable
def minDeg (I : Ideal (MvPolynomial α F)) := sInf {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥}


@[simp] lemma minDeg_bot : minDeg (⊥ : Ideal (MvPolynomial α F)) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  right; apply Set.subset_empty_iff.mp
  intro n hn; rw [Set.mem_setOf] at hn
  specialize hn homoSubI_zero
  contradiction

@[simp] lemma minDeg_top : minDeg (⊤ : Ideal (MvPolynomial α F)) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left; rw [Set.mem_setOf]
  apply (Submodule.ne_bot_iff (homogeneousSubmodule α F 0 ⊓ Submodule.restrictScalars F ⊤)).mpr
  use 1; constructor; swap; exact Ne.symm (zero_ne_one' (MvPolynomial α F))
  apply Submodule.mem_inf.mpr; constructor
  rw [mem_homogeneousSubmodule]; exact isHomogeneous_one α F
  simp only [Submodule.restrictScalars_top, Submodule.mem_top]

lemma minDeg_mem (h : minDeg I ≠ 0) : minDeg I ∈ {n : ℕ | (homogeneousSubmoduleI n I) ≠ ⊥} := by
  apply Nat.sInf_mem
  contrapose! h
  unfold minDeg; rw [h]
  apply Nat.sInf_empty

lemma top_of_zero_mem_minDeg : 0 ∈ {n | homogeneousSubmoduleI n I ≠ ⊥} → I = ⊤ := by
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

lemma bot_of_empty_minDeg (h : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) :
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

lemma minDeg_zero_iff (h : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) :
  minDeg I = 0 ↔ I = ⊤ ∨ I = ⊥ := by
    constructor; swap; intro hI
    rcases hI with hIT|hIB
    rw [hIT]; exact minDeg_top
    rw [hIB]; exact minDeg_bot

    intro hI
    apply Nat.sInf_eq_zero.mp at hI
    rcases hI with hIT|hIB
    left; exact top_of_zero_mem_minDeg hIT
    right; exact bot_of_empty_minDeg h hIB


lemma zero_of_minDeg_zero (hh : Ideal.IsHomogeneous (homogeneousSubmodule α F) I) (hIT : I ≠ ⊤) :
  minDeg I = 0 → I = 0 := by
    intro hI
    apply Nat.sInf_eq_zero.mp at hI
    let hIT := hIT ∘ top_of_zero_mem_minDeg
    rw [imp_false] at hIT
    simp only [hIT, false_or] at hI
    exact bot_of_empty_minDeg hh hI

lemma nonzero_homo_of_minDeg_nonzero (h : minDeg I ≠ 0) : ∃ p ∈ I, p ≠ 0 ∧ p.IsHomogeneous (minDeg I) := by
  apply minDeg_mem at h
  rw [Set.mem_setOf] at h
  apply Submodule.exists_mem_ne_zero_of_ne_bot at h
  obtain ⟨p, h⟩ := h
  use p; constructor
  exact (Submodule.mem_inf.mp h.1).2
  constructor; exact h.2
  apply And.left at h;
  apply Submodule.mem_inf.mp at h
  exact (mem_homogeneousSubmodule (minDeg I) p).mp h.1


@[simp] lemma ideal_span_subset_zero_singleton {S : Set (MvPolynomial α F)} (h : S ⊆ {0}) : Ideal.span S = 0 := by
  apply Set.subset_singleton_iff_eq.mp at h
  rcases h with h|h
  rw [h, Ideal.span_empty, Ideal.zero_eq_bot];
  rw [h, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

theorem minDeg_antitone {I J : Ideal (MvPolynomial α F)} (hI : Ideal.IsHomogeneous (homogeneousSubmodule α F) I)
  (hb : I ≠ ⊥) : I ≤ J →  minDeg I ≥ minDeg J := by
    intro hIJ
    by_cases hbt : minDeg I = 0
    simp only [minDeg_zero_iff hI, hb, or_false] at hbt
    rw [hbt, top_le_iff] at hIJ
    rw [hIJ, hbt, minDeg_top]

    apply Nat.sInf_le
    rw [Set.mem_setOf]
    let hmd := minDeg_mem hbt
    rw [Set.mem_setOf, ← bot_lt_iff_ne_bot] at hmd
    rw [← bot_lt_iff_ne_bot]
    apply lt_of_lt_of_le hmd (homoSubI_monotone (minDeg I) hIJ)

@[simp] theorem minDeg_homo [DecidableEq α] {n : ℕ} {S : Set (MvPolynomial α F)} (hS : ∃ p ∈ S, p ≠ 0) (h : S ⊆ homogeneousSubmodule α F n) :
minDeg (Ideal.span S) = n := by
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
