import EnvyFreeResearch.Full.UpperFloatingKernel
import EnvyFreeResearch.Full.UpperFloatingCount

/-! The finite linear-algebra step for whole-cell multicolor discrepancy.
Every cell sum is maintained; a changing finite set of observer/color
equations is maintained. Integral coordinates stay fixed permanently. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Multicolor
open UpperFloating UpperFloatingStep
open scoped Classical BigOperators

variable {Observer Cell Color : Type*}
  [Fintype Observer] [Fintype Cell] [Fintype Color]

def coefficients (w : Observer → Cell → ℝ) (active : Finset (Observer × Color)) :
    (Cell ⊕ active) → (Cell × Color) → ℝ
  | .inl e, c => if c.1 = e then 1 else 0
  | .inr row, c => if c.2 = row.val.2 then w row.val.1 c.1 else 0

def moment (w : Observer → Cell → ℝ) (x : Cell × Color → ℝ) (row : Observer × Color) : ℝ :=
  ∑ e, w row.1 e*x (e,row.2)

theorem cell_equation (w : Observer → Cell → ℝ) (active : Finset (Observer × Color))
    (x : Cell × Color → ℝ) (e : Cell) :
    linearValue (coefficients w active) x (.inl e) = ∑ j, x (e,j) := by
  unfold linearValue
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ f : Cell, if f=e then ∑ j, x (f,j) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases h : f=e <;> simp [coefficients,h]
    _ = ∑ j, x (e,j) := by simp

theorem moment_equation (w : Observer → Cell → ℝ) (active : Finset (Observer × Color))
    (x : Cell × Color → ℝ) (row : active) :
    linearValue (coefficients w active) x (.inr row) = moment w x row := by
  simp [linearValue,coefficients,moment,Fintype.sum_prod_type]

theorem supported_zero_off_split (x d : Cell × Color → ℝ)
    (hsupport : ∀ c, d c ≠ 0 → c ∈ fractional x) (e : Cell) (he : e ∉ splitCells x)
    (j : Color) : d (e,j) = 0 := by
  by_contra hn
  exact he (Finset.mem_image.mpr ⟨(e,j),hsupport _ hn,rfl⟩)

theorem fractional_card_le (w : Observer → Cell → ℝ) (active : Finset (Observer × Color))
    (x : Cell × Color → ℝ) (hkernel : NoFractionalKernel (coefficients w active) x) :
    (fractional x).card ≤ (splitCells x).card+active.card := by
  let reduced : (splitCells x ⊕ active) → (Cell × Color) → ℝ :=
    fun r => coefficients w active (r.map Subtype.val id)
  have hr : ∀ d : Cell × Color → ℝ, (∀ c, d c ≠ 0 → c ∈ fractional x) →
      (∀ r, linearValue reduced d r = 0) → d=0 := by
    intro d hs hd
    apply hkernel d hs
    intro r
    cases r with
    | inl e =>
      by_cases he : e ∈ splitCells x
      · exact hd (.inl ⟨e,he⟩)
      · rw [cell_equation]
        exact Finset.sum_eq_zero (fun j _ => supported_zero_off_split x d hs e he j)
    | inr row => exact hd (.inr row)
  have h := supported_kernel_card_bound reduced (fractional x) hr
  simpa only [Fintype.card_sum,Fintype.card_coe] using h

theorem fractional_le_twice_active (w : Observer → Cell → ℝ) (active : Finset (Observer × Color))
    (x : Cell × Color → ℝ) (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1)
    (hrow : ∀ e, ∑ j, x (e,j)=1) (hkernel : NoFractionalKernel (coefficients w active) x) :
    (fractional x).card ≤ 2*active.card := by
  have hlow := twice_split_le_fractional x hbox hrow
  have hhigh := fractional_card_le w active x hkernel
  omega

theorem exists_basic (w : Observer → Cell → ℝ) (active : Finset (Observer × Color))
    (initial : Cell × Color → ℝ) (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e,j)=1) :
    ∃ x : Cell × Color → ℝ,
      (∀ c, 0 ≤ x c ∧ x c ≤ 1) ∧ (∀ e, ∑ j, x (e,j)=1) ∧
      (∀ row ∈ active, moment w x row = moment w initial row) ∧
      Frozen initial x ∧ (fractional x).card ≤ 2*active.card := by
  obtain ⟨x,hx,hkernel⟩ := exists_frozen_basic (coefficients w active)
    (linearValue (coefficients w active) initial) initial ⟨hbox,fun _ => rfl⟩
  have hrowx (e : Cell) : ∑ j, x (e,j)=1 := by
    rw [← cell_equation w active x e,hx.1.2,cell_equation,hrow]
  refine ⟨x,hx.1.1,hrowx,?_,hx.2,fractional_le_twice_active w active x hx.1.1 hrowx hkernel⟩
  intro row hmem
  exact (moment_equation w active x ⟨row,hmem⟩).symm.trans
    ((hx.1.2 (.inr ⟨row,hmem⟩)).trans (moment_equation w active initial ⟨row,hmem⟩))

end EnvyFreeResearch.Full.Chores.Multicolor
