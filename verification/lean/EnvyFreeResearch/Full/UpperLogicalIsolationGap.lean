import EnvyFreeResearch.Full.UpperLogicalPreparationGuard
import EnvyFreeResearch.Full.UpperPreparedIsolation
import EnvyFreeResearch.Full.UpperBatchPermutation

/-!
# The witness reserve gap is the actual correction-table disagreement

The full fine cache is normalized by old-buffer mass. Its row multipliers
use the actual recorded reserve totals. Restricting to retained fine indices
therefore gives exactly the correction table, including every zero cell.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalIsolation

open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRecordedQuantiles UpperWitnessExtraction UpperGridCells Chores

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell] [DecidableEq Cell]

omit [Fintype Agent] [Fintype Cell] [DecidableEq Cell] in
theorem difference_le_reserveGap (values : Agent → Cell → ℝ) (normalizer : Agent → ℝ)
    (reserve : Finset Cell) (i j : Agent) (e : Cell) (he : e ∈ reserve) :
    |scaledDifference values normalizer i j e| ≤ reserveGap values normalizer reserve i j := by
  have hne : reserve.Nonempty := ⟨e, he⟩
  rw [reserveGap, dite_eq_left hne]
  exact Finset.le_sup' (fun e => |scaledDifference values normalizer i j e|) he

omit [Fintype Agent] in
/-- Padding a reserve-index table by zero leaves the exact maximum reserve
row disagreement, rather than the full-buffer disagreement. -/
theorem cellGap_scaled_restriction (values : Agent → Cell → ℝ) (normalizer : Agent → ℝ)
    (reserve : Finset Cell) (i j : Agent) :
    UpperPayments.cellGap (fun r e => if e ∈ reserve then normalizer r * values r e else 0) i j =
      reserveGap values normalizer reserve i j := by
  apply le_antisymm
  · unfold UpperPayments.cellGap
    split_ifs with h
    · apply Finset.sup'_le
      intro e _
      by_cases he : e ∈ reserve
      · simpa only [he, ite_true, scaledDifference] using difference_le_reserveGap values normalizer reserve i j e he
      · simp only [he, ite_false, sub_self, abs_zero]
        exact reserveGap_nonnegative values normalizer reserve i j
    · exact reserveGap_nonnegative values normalizer reserve i j
  · by_cases hr : reserve.Nonempty
    · rw [reserveGap, dite_eq_left hr]
      apply Finset.sup'_le
      intro e he
      simpa only [he, ite_true, scaledDifference] using UpperPayments.difference_le_cellGap
        (fun r e => if e ∈ reserve then normalizer r * values r e else 0) i j e
    · rw [reserveGap, dite_eq_right hr]
      exact UpperPayments.cellGap_nonneg _ i j

variable {n k : ℕ}

def multipliers (active : Fin k → Fin n) (origin reserve : State n) (i : Fin k) : ℝ :=
  total origin (active i) / total reserve (active i)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

/-- Equality of the two actual cached computations; no scaled-table identity
is supplied by a caller. Division by a zero reserve is total on both sides. -/
theorem reserve_table_eq_scaled (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (count (Agent := Fin k) q + 1) → I) (i : Fin k)
    (e : Fin (count (Agent := Fin k) q + m + 1)) :
    UpperCorrectionSetup.table active (reserveState policy active origin q m draw theta labels)
      (UpperGridMerge.cuts policy active origin q m draw) i e =
        if e ∈ reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels then
          multipliers active origin (reserveState policy active origin q m draw theta labels) i *
            UpperGridCache.table policy active origin q m draw i e else 0 := by
  unfold UpperCorrectionSetup.table multipliers
  rw [reserveState_cachedMass μ policy hpolicy active origin hgood hpositive,
    total_correct μ origin hgood,
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels),
    UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
  split_ifs
  · field_simp [(hpositive i).ne']
  · simp

/-- The exact `A` used by correction setup equals the computed surviving-cell
witness gap. The full finite table retains zero entries outside the reserve. -/
theorem reserve_cellGap (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (count (Agent := Fin k) q + 1) → I) (i j : Fin k) :
    UpperPayments.cellGap
      (UpperCorrectionSetup.table active (reserveState policy active origin q m draw theta labels)
        (UpperGridMerge.cuts policy active origin q m draw)) i j =
      reserveGap (UpperGridCache.table policy active origin q m draw)
        (multipliers active origin (reserveState policy active origin q m draw theta labels))
        (reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels) i j := by
  exact (congrArg (fun (table : Fin k → Fin (count (Agent := Fin k) q + m + 1) → ℝ) =>
    UpperPayments.cellGap table i j)
    (funext (fun r => funext (fun e => reserve_table_eq_scaled μ policy hpolicy active origin hgood hpositive
      q m draw theta labels r e)))).trans
    (cellGap_scaled_restriction (UpperGridCache.table policy active origin q m draw)
      (multipliers active origin (reserveState policy active origin q m draw theta labels))
      (reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels) i j)

end Correctness

end EnvyFreeResearch.Full.UpperLogicalIsolation
