import EnvyFreeResearch.Full.UpperFloatingKernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Finite candidates for floating

A pattern marks each coordinate as zero, one, or free. Original equations
plus the fixed-coordinate rows have full column rank at every basic point.
The explicit Gram inverse reconstructs that point. Its real coordinates are
Borel functions of the cached equation coefficients and right-hand side.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Matrix

namespace EnvyFreeResearch.Full.UpperFloating

open UpperFloatingStep

variable {Coord Equation : Type*} [Fintype Coord] [Fintype Equation]

abbrev Pattern (Coord : Type*) := Coord → Option Bool

def patternOf (x : Coord → ℝ) : Pattern Coord := fun c =>
  if x c = 0 then some false else if x c = 1 then some true else none

def augmented (A : Equation → Coord → ℝ) (p : Pattern Coord) :
    Matrix (Equation ⊕ Coord) Coord ℝ
  | .inl r, c => A r c
  | .inr r, c => match p r with
    | none => 0
    | some _ => if c = r then 1 else 0

def augmentedRhs (b : Equation → ℝ) (p : Pattern Coord) : Equation ⊕ Coord → ℝ
  | .inl r => b r
  | .inr r => match p r with
    | some true => 1
    | _ => 0

omit [Fintype Equation] in
theorem augmented_fixed_row (A : Equation → Coord → ℝ) (p : Pattern Coord)
    (d : Coord → ℝ) (c : Coord) :
    linearValue (augmented A p) d (.inr c) = match p c with
      | none => 0
      | some _ => d c := by
  cases h : p c <;> simp [linearValue, augmented, h]

theorem augmented_solution (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (x : Coord → ℝ) (hx : ∀ r, linearValue A x r = b r) :
    (augmented A (patternOf x)).mulVec x = augmentedRhs b (patternOf x) := by
  funext r
  cases r with
  | inl r => exact hx r
  | inr c =>
    change linearValue (augmented A (patternOf x)) x (.inr c) = _
    rw [augmented_fixed_row]
    by_cases h0 : x c = 0
    · simp [patternOf, augmentedRhs, h0]
    · by_cases h1 : x c = 1 <;> simp [patternOf, augmentedRhs, h0, h1]

theorem augmented_injective (A : Equation → Coord → ℝ) (x : Coord → ℝ)
    (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hkernel : NoFractionalKernel A x) :
    Function.Injective (augmented A (patternOf x)).mulVec := by
  change Function.Injective (Matrix.mulVecLin (augmented A (patternOf x)))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro d hd
  apply hkernel d
  · intro c hdc
    by_contra hn
    have hnot : ¬(0 < x c ∧ x c < 1) := by simpa [fractional] using hn
    have hboundary : x c = 0 ∨ x c = 1 := by
      have hc := hbox c
      by_cases h0 : x c = 0
      · exact Or.inl h0
      · right
        have hp : 0 < x c := lt_of_le_of_ne hc.1 (Ne.symm h0)
        exact le_antisymm hc.2 (le_of_not_gt (fun hlt => hnot ⟨hp, hlt⟩))
    have hfixed := congrFun hd (.inr c)
    change linearValue (augmented A (patternOf x)) d (.inr c) = 0 at hfixed
    rw [augmented_fixed_row] at hfixed
    rcases hboundary with h0 | h1
    · exact hdc (by simpa [patternOf, h0] using hfixed)
    · exact hdc (by simpa [patternOf, h1] using hfixed)
  · intro r
    exact congrFun hd (.inl r)

def gram (A : Equation → Coord → ℝ) (p : Pattern Coord) : Matrix Coord Coord ℝ :=
  (augmented A p)ᵀ * augmented A p

/-- Total rational candidate, assigned the usual zero inverse when the Gram
matrix is singular. Singular candidates are rejected by the finite test. -/
def candidate (A : Equation → Coord → ℝ) (b : Equation → ℝ) (p : Pattern Coord) : Coord → ℝ :=
  (gram A p)⁻¹.mulVec ((augmented A p)ᵀ.mulVec (augmentedRhs b p))

/-- The candidate corresponding to the actual zero/one/free pattern of a
basic feasible point is exactly that point. -/
theorem candidate_patternOf (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (x : Coord → ℝ) (hx : Feasible A b x) (hkernel : NoFractionalKernel A x) :
    candidate A b (patternOf x) = x := by
  classical
  have hpos : (gram A (patternOf x)).PosDef := by
    simpa [gram] using Matrix.PosDef.conjTranspose_mul_self
      (augmented A (patternOf x)) (augmented_injective A x hx.1 hkernel)
  have hunit : IsUnit (gram A (patternOf x)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  unfold candidate
  rw [← augmented_solution A b x hx.2]
  rw [Matrix.mulVec_mulVec x (augmented A (patternOf x))ᵀ (augmented A (patternOf x))]
  change (gram A (patternOf x))⁻¹.mulVec ((gram A (patternOf x)).mulVec x) = x
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem matrix_inverse_entry_measurable (M : X → Matrix Coord Coord ℝ)
    (hM : ∀ i j, Measurable (fun z => M z i j)) (i j : Coord) :
    Measurable (fun z => (M z)⁻¹ i j) := by
  classical
  have hm : Measurable M := Measurable.of_eval_matrix M hM
  have hd : Measurable (fun z => (M z).det) :=
    (continuous_id.matrix_det.measurable).comp hm
  have hadj : Measurable (fun z => (M z).adjugate) :=
    (continuous_id.matrix_adjugate.measurable).comp hm
  have h : Measurable (fun z => ((M z).det)⁻¹ * (M z).adjugate i j) :=
    hd.inv.mul (hadj.eval_matrix (i := i) (j := j))
  convert h using 1
  funext z
  simp [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul]

theorem candidate_measurable (A : X → Equation → Coord → ℝ) (b : X → Equation → ℝ)
    (hA : ∀ r c, Measurable (fun z => A z r c))
    (hb : ∀ r, Measurable (fun z => b z r)) (p : Pattern Coord) (c : Coord) :
    Measurable (fun z => candidate (A z) (b z) p c) := by
  have haug (r : Equation ⊕ Coord) (i : Coord) :
      Measurable (fun z => augmented (A z) p r i) := by
    cases r with
    | inl r => exact hA r i
    | inr r => exact measurable_const
  have hrhs (r : Equation ⊕ Coord) : Measurable (fun z => augmentedRhs (b z) p r) := by
    cases r with
    | inl r => exact hb r
    | inr r => exact measurable_const
  have hgram (i j : Coord) : Measurable (fun z => gram (A z) p i j) :=
    Finset.measurable_sum _ (fun r _ => (haug r i).mul (haug r j))
  have hinv := matrix_inverse_entry_measurable (fun z => gram (A z) p) hgram
  exact Finset.measurable_sum _ (fun i _ => (hinv c i).mul
    (Finset.measurable_sum _ (fun r _ => (haug r i).mul (hrhs r))))

end Measurability

end EnvyFreeResearch.Full.UpperFloating
