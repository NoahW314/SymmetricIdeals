import Mathlib


open MvPolynomial

variable {F : Type*} [CommSemiring F]
variable {α : Type*}

noncomputable
def min_gen_size (R : Type*) [Semiring R] (I : Ideal R) : ℕ
  := sInf { n : ℕ | ∃ S : Finset R, S.card = n ∧ I = Ideal.span ↑S}
noncomputable abbrev μ := min_gen_size


variable {I : Ideal (MvPolynomial α F)}
def idl : α → ℕ → ℕ := fun _ n => n
def expSum : (α →₀ ℕ) →+ ℕ := ⟨⟨fun s : (α →₀ ℕ) => (Finsupp.sum s idl), by exact Finsupp.sum_zero_index⟩, by
  simp only; intro s t
  exact Finsupp.sum_add_index' (congrFun rfl) fun a b₁ ↦ congrFun rfl
  ⟩
def stdGrade (α : Type*) (F : Type*) [CommSemiring F] : ℕ → Submodule F (MvPolynomial α F)
  := AddMonoidAlgebra.gradeBy F expSum

noncomputable
instance stdGradeRing : GradedAlgebra (stdGrade α F) := by
  unfold stdGrade
  apply AddMonoidAlgebra.gradeBy.gradedAlgebra expSum



def homogeneousSubmoduleI (n : ℕ) (I : Ideal (MvPolynomial α F)) : Submodule F (MvPolynomial α F) :=
  (homogeneousSubmodule α F n) ⊓ (Submodule.restrictScalars F I)

-- Is the ideal generated in a single degree?  (Note: this implies that the ideal is homogeneous)
def IsSingleDegGenI (I : Ideal (MvPolynomial α F)) := I = Ideal.span (homogeneousSubmoduleI
  (sInf {n : ℕ | n ≠ 0 ∧ (homogeneousSubmoduleI n I) ≠ ⊥}) I)


theorem single_deg_gen_homo (h : IsSingleDegGenI I) : Ideal.IsHomogeneous (stdGrade α F) I := by
  refine (Ideal.IsHomogeneous.iff_exists (stdGrade α F) I).mpr ?_
  let n := sInf {k : ℕ | k ≠ 0 ∧ (homogeneousSubmoduleI k I) ≠ ⊥}
  let M := homogeneousSubmoduleI n I
  let S' := SetLike.homogeneousSubmonoid (stdGrade α F)
  have hM : ∀ m : M, m.1 ∈ S' := by
    intro m; unfold S' SetLike.homogeneousSubmonoid
    apply Submonoid.mem_carrier.mp
    simp only; rw [Set.mem_setOf]
    unfold SetLike.IsHomogeneousElem

    let hm := m.2; unfold M homogeneousSubmoduleI at hm
    apply Submodule.mem_inf.mp at hm; apply And.left at hm
    apply (Submodule.mem_carrier (homogeneousSubmodule α F n)).mpr at hm
    unfold homogeneousSubmodule at hm; simp only at hm
    rw [Set.mem_setOf] at hm; unfold IsHomogeneous IsWeightedHomogeneous at hm

    use n
    simp only [stdGrade, Submodule.mem_mk, Finsupp.mem_support_iff, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk]
    apply Set.mem_setOf.mpr
    intro s hms
    specialize hm hms
    simp only [expSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; unfold idl
    simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
      id_eq, smul_eq_mul, mul_one] at hm
    exact hm
  let fm : M → S' := fun m => ⟨m, by exact hM m⟩
  let S := Set.range fm
  use S; rw [h]; congr

  ext p; constructor; intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right, S, S',
    fm, M]
  rw [SetLike.mem_coe] at h
  use hM ⟨p, h⟩; use p; use h

  intro h
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right, S', fm, M, S] at h
  rw [SetLike.mem_coe]
  obtain ⟨_, q, hp, hpq⟩ := h
  apply Subtype.mk_eq_mk.mp at hpq
  rw [hpq] at hp
  exact hp
