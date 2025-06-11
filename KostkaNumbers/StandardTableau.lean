import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Combinatorics.Enumerative.Partition

structure StandardYoungTableau (μ : YoungDiagram) where
  entry : ℕ → ℕ → ℕ
  row_strict : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 < entry i j2
  col_strict : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j
  zeros : ∀ {i j}, (i, j) ∉ μ → entry i j = 0
  /- a standard young tableau should contain all entry from 0 to n-1 where n is the number
  of cells in the Young diagram -/
  largest : ∀ {i j : ℕ}, entry i j < μ.card
  inj : ∀ {i1 i2 j1 j2 : ℕ}, (i1, j1) ∈ μ → (i2, j2) ∈ μ → entry i1 j1 = entry i2 j2 → (i1, j1) = (i2, j2)

namespace StandardYoungTableau

instance instFunLike {μ : YoungDiagram} : FunLike (StandardYoungTableau μ) ℕ (ℕ → ℕ) where
  coe := StandardYoungTableau.entry
  coe_injective' T T' h := by
    cases T
    cases T'
    congr

@[simp]
theorem to_fun_eq_coe {μ : YoungDiagram} {T : StandardYoungTableau μ} :
  T.entry = (T : ℕ → ℕ → ℕ) := rfl

@[ext]
theorem ext {μ : YoungDiagram} {T T' : StandardYoungTableau μ} (h : ∀ i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun _ ↦ by
    funext
    apply h




def filling {μ : YoungDiagram} (T : StandardYoungTableau μ) (i j : ℕ) : Finset.range μ.card :=
    have h : T.entry i j < μ.card := by exact T.largest
    have h2 : T.entry i j ∈ Finset.range μ.card := by rw[← Finset.mem_range] at h; exact h
    ⟨T.entry i j, h2⟩
def fill (μ : YoungDiagram) (T : StandardYoungTableau μ) (p : μ) : Finset.range μ.card :=
  filling T p.1.1 p.1.2
def fill_func (μ : YoungDiagram) (T : StandardYoungTableau μ) : Nat.Partition μ.card := sorry


theorem fill_inj {μ : YoungDiagram} : Function.Injective (fill_func μ) := sorry


noncomputable
instance (μ : YoungDiagram) : Fintype (StandardYoungTableau μ) :=
  Fintype.ofInjective (fill_func μ) fill_inj

--def shape (n : ℕ) : Finset YoungDiagram :=
--  Finset.univ.filter fun μ => μ.card = n

def shape (n : ℕ) : Set YoungDiagram := {μ : YoungDiagram | μ.card = n}
--def shapePart {n : ℕ} (p : Nat.Partition n) : Set YoungDiagram := {μ : YoungDiagram | List.mergeSort p.parts.toList ≥ = μ.rowLens }

theorem finiteShape (n : ℕ) : Finite (shape n) := sorry
