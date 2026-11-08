import EnvyFreeResearch.Full.UpperGlobalRunTerminationCounts
import EnvyFreeResearch.Full.UpperGlobalRunTerminationMeasurable

/-! Almost-sure termination of the actual global state machine from a finite
expected number of its actual paid calls. The expected bound remains an
explicit input to be discharged by global runtime accounting. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal BigOperators
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperExpectedRuntime
variable {n : ℕ}

theorem paidCount_eq_three (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (initial : Phase n) (omega : Stream (Universal n)) :
    paidCount policy fallback chores initial omega =
      attempts (paidEvent policy fallback chores initial .snapshot) omega +
      attempts (paidEvent policy fallback chores initial .shrink) omega +
      attempts (paidEvent policy fallback chores initial .repair) omega := by
  unfold paidCount
  rw [show (Finset.univ : Finset Kind)={.snapshot,.shrink,.repair} from rfl]
  simp [add_assoc]

theorem terminates_of_measurable_step_paid_mean (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (initial : Phase n) (law : Measure (Stream (Universal n)))
    (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hmean : (∫⁻ omega, paidCount policy fallback chores initial omega ∂law) ≤ bound) :
    ∀ᵐ omega ∂law, finishedRun policy fallback chores initial omega :=
  terminates_of_paid_mean policy fallback chores initial law
    (paidEvent_measurable policy fallback chores hstep initial) bound hfinite hmean

end EnvyFreeResearch.Full.UpperGlobalPhysical
