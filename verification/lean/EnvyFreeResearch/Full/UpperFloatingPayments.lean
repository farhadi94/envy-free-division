import EnvyFreeResearch.Full.UpperFloatingKernel
import EnvyFreeResearch.Full.UpperFloatingCount

/-!
# Floating the actual reserve-payment equations

The equations are one sum per cell and one moment per observer/recipient
pair. The unused color has no moment equation. On a fractional kernel vector,
only the split-cell sum equations can contribute to the rank.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloating

open UpperFloatingStep

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

abbrev PaymentCoord (Agent Cell : Type*) := Cell × Option Agent
abbrev PaymentEquation (Agent Cell : Type*) := Cell ⊕ (Agent × Agent)

def coefficients (a : Agent → Cell → ℝ) :
    PaymentEquation Agent Cell → PaymentCoord Agent Cell → ℝ
  | .inl e, c => if c.1 = e then 1 else 0
  | .inr (i, j), c => if c.2 = some j then a i c.1 else 0

theorem cell_equation (a : Agent → Cell → ℝ) (x : PaymentCoord Agent Cell → ℝ) (e : Cell) :
    linearValue (coefficients a) x (.inl e) = ∑ j, x (e, j) := by
  unfold linearValue
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ f : Cell, if f = e then ∑ j, x (f, j) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases h : f = e <;> simp [coefficients, h]
    _ = ∑ j, x (e, j) := by simp

theorem moment_equation (a : Agent → Cell → ℝ) (x : PaymentCoord Agent Cell → ℝ) (i j : Agent) :
    linearValue (coefficients a) x (.inr (i, j)) = ∑ e, a i e * x (e, some j) := by
  simp [linearValue, coefficients, Fintype.sum_prod_type]

/-- A supported fractional direction vanishes on every nonsplit cell. -/
theorem supported_zero_off_split (x d : PaymentCoord Agent Cell → ℝ)
    (hsupport : ∀ c, d c ≠ 0 → c ∈ fractional x) (e : Cell) (he : e ∉ splitCells x)
    (j : Option Agent) : d (e, j) = 0 := by
  by_contra hn
  exact he (Finset.mem_image.mpr ⟨(e, j), hsupport _ hn, rfl⟩)

/-- The actual rank count: only split cell-sum rows and the `k²` moment
rows are needed to detect supported kernel directions. -/
theorem fractional_card_le_split_add_square (a : Agent → Cell → ℝ)
    (x : PaymentCoord Agent Cell → ℝ) (hkernel : NoFractionalKernel (coefficients a) x) :
    (fractional x).card ≤ (splitCells x).card + Fintype.card Agent ^ 2 := by
  let reduced : (splitCells x ⊕ (Agent × Agent)) → PaymentCoord Agent Cell → ℝ :=
    fun r => coefficients a (r.map Subtype.val id)
  have hr : ∀ d : PaymentCoord Agent Cell → ℝ, (∀ c, d c ≠ 0 → c ∈ fractional x) →
      (∀ r, linearValue reduced d r = 0) → d = 0 := by
    intro d hs hd
    apply hkernel d hs
    intro r
    cases r with
    | inl e =>
      by_cases he : e ∈ splitCells x
      · exact hd (.inl ⟨e, he⟩)
      · rw [cell_equation]
        exact Finset.sum_eq_zero (fun j _ => supported_zero_off_split x d hs e he j)
    | inr ij => exact hd (.inr ij)
  have h := supported_kernel_card_bound reduced (fractional x) hr
  simpa [Fintype.card_sum, Fintype.card_prod, pow_two] using h

theorem split_card_le_square (a : Agent → Cell → ℝ) (x : PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hrow : ∀ e, ∑ j, x (e, j) = 1)
    (hkernel : NoFractionalKernel (coefficients a) x) :
    (splitCells x).card ≤ Fintype.card Agent ^ 2 := by
  have hlow := twice_split_le_fractional x hbox hrow
  have hhigh := fractional_card_le_split_add_square a x hkernel
  omega

/-- General reserve floating from any initial feasible colored assignment.
All observer-recipient moments and all original integral coordinates are
preserved, with at most `k²` split cells at the final point. -/
theorem exists_floated_basic (a : Agent → Cell → ℝ)
    (initial : PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e, j) = 1) :
    ∃ x, FrozenFeasible (coefficients a) (linearValue (coefficients a) initial) initial x ∧
      (splitCells x).card ≤ Fintype.card Agent ^ 2 ∧
      NoFractionalKernel (coefficients a) x := by
  obtain ⟨x, hx, hkernel⟩ := exists_frozen_basic (coefficients a)
    (linearValue (coefficients a) initial) initial ⟨hbox, fun _ => rfl⟩
  have hrowx (e : Cell) : ∑ j, x (e, j) = 1 := by
    rw [← cell_equation a x e, hx.1.2, cell_equation, hrow]
  exact ⟨x, hx, split_card_le_square a x hx.1.1 hrowx hkernel, hkernel⟩

theorem exists_floated (a : Agent → Cell → ℝ) (initial : PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e, j) = 1) :
    ∃ x : PaymentCoord Agent Cell → ℝ,
      (∀ c, 0 ≤ x c ∧ x c ≤ 1) ∧
      (∀ e, ∑ j, x (e, j) = 1) ∧
      (∀ i j, (∑ e, a i e * x (e, some j)) = ∑ e, a i e * initial (e, some j)) ∧
      Frozen initial x ∧ (splitCells x).card ≤ Fintype.card Agent ^ 2 := by
  obtain ⟨x, hx, hcount, _⟩ := exists_floated_basic a initial hbox hrow
  refine ⟨x, hx.1.1, ?_, ?_, hx.2, hcount⟩
  · intro e
    rw [← cell_equation a x e, hx.1.2, cell_equation, hrow]
  · intro i j
    rw [← moment_equation a x i j, hx.1.2, moment_equation]

end EnvyFreeResearch.Full.UpperFloating
