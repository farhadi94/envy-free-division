import EnvyFreeResearch.Full.NonnegativeExperiment
import EnvyFreeResearch.Full.NonnegativeReplay
import EnvyFreeResearch.Full.NonnegativeSuccess

namespace EnvyFreeResearch.Full.NonnegativeRetainedFailure

open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativeReplay NonnegativeSuccess
open NonnegativeAllocation NonnegativeFailure NonnegativeRandomOutput
open NonnegativeAllocationDecoder NonnegativeEndpointLaw NonnegativeShift NonnegativeExperiment
open scoped Classical

abbrev Circle := NonnegativeCircle.Circle

def Fair {Agent : Type*} (chores : Bool) (rows : Agent → MixedDensity.Row)
    (A : Allocation Agent) : Prop := if chores then ChoreEF rows A else CakeEF rows A

def SafeOutput {Agent : Type*} (A : Allocation Agent) (h c d : ℝ) : Prop :=
  (∀ k, h / 2 < |c - A.left k|) ∧ (∀ k, h / 2 < |c - A.right k|) ∧
  (∀ k, h / 2 < |d - A.left k|) ∧ (∀ k, h / 2 < |d - A.right k|)

def Favorable {Agent : Type*} (chores : Bool) (A : Allocation Agent)
    (observer : Agent) (z : ℝ × Circle) : Prop :=
  circleOwner A (first z) ≠ circleOwner A (second z) ∧
    observer ≠ (if chores then circleOwner A (second z) else circleOwner A (first z))

/-- The literal successful-output decoder fails actual fairness in either
orientation. Only physical output endpoints enter the avoidance premise. -/
theorem decoded_failure {n : ℕ} (chores : Bool) (A : Allocation (Fin n))
    (observer : Fin n) (z : ℝ × Circle) (h : ℝ) (hh : 0 < h)
    (hc0 : 0 < realFirst z - h / 2) (hc1 : realFirst z + h / 2 < 1)
    (hd0 : 0 < realSecond z - h / 2) (hd1 : realSecond z + h / 2 < 1)
    (hsafe : SafeOutput A h (realFirst z) (realSecond z))
    (huniform : UniformEF A) (hfavorable : Favorable chores A observer z) :
    ¬ Fair chores (inputRows h (observer, z)) A := by
  have hcoeC : (realFirst z : Circle) = first z := representative_coe _
  have hcoeD : (realSecond z : Circle) = second z := representative_coe _
  have hownerC : circleOwner A (first z) = ownerAt A (realFirst z) := rfl
  have hownerD : circleOwner A (second z) = ownerAt A (realSecond z) := rfl
  have hrow : inputRows h (observer, z) observer =
      NonnegativePulse.row h (realFirst z : Circle) (realSecond z : Circle) := by
    simp [inputRows, perturbedRows, hcoeC, hcoeD]
  cases chores with
  | false =>
    have hf : ownerAt A (realFirst z) ≠ ownerAt A (realSecond z) ∧
        observer ≠ ownerAt A (realFirst z) := by
      simpa only [Favorable, Bool.false_eq_true, ite_false, hownerC, hownerD] using hfavorable
    have hequal : volume.real (A.share observer) = volume.real (A.share (ownerAt A (realFirst z))) :=
      le_antisymm (huniform _ _) (huniform _ _)
    have henvy := cake_strict_envy A h (realFirst z) (realSecond z) hh hc0 hc1 hd0 hd1
      hsafe.1 hsafe.2.1 hsafe.2.2.1 hsafe.2.2.2 observer hf.2 hf.1 hequal
    intro hfair
    have hcompare := hfair observer (ownerAt A (realFirst z))
    rw [hrow] at hcompare
    exact (not_lt_of_ge hcompare) henvy
  | true =>
    have hf : ownerAt A (realFirst z) ≠ ownerAt A (realSecond z) ∧
        observer ≠ ownerAt A (realSecond z) := by
      simpa only [Favorable, ite_true, hownerC, hownerD] using hfavorable
    have hequal : volume.real (A.share observer) = volume.real (A.share (ownerAt A (realSecond z))) :=
      le_antisymm (huniform _ _) (huniform _ _)
    have henvy := chore_strict_envy A h (realFirst z) (realSecond z) hh hc0 hc1 hd0 hd1
      hsafe.1 hsafe.2.1 hsafe.2.2.1 hsafe.2.2.2 observer hf.2 hf.1 hequal
    intro hfair
    have hcompare := hfair observer (ownerAt A (realSecond z))
    rw [hrow] at hcompare
    exact (not_lt_of_ge hcompare) henvy

/-- Old physical failures also survive for both orientations, using the
measurable max-minus-min gap of the actual output. -/
theorem old_failure {n : ℕ} [NeZero n] (chores : Bool) (A : Allocation (Fin n))
    (observer : Fin n) (z : ℝ × Circle) (h : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < realFirst z - h / 2) (hc1 : realFirst z + h / 2 < 1)
    (hd0 : 0 < realSecond z - h / 2) (hd1 : realSecond z + h / 2 < 1)
    (hgap : h < uniformGap A) : ¬ Fair chores (inputRows h (observer, z)) A := by
  have hcoeC : (realFirst z : Circle) = first z := representative_coe _
  have hcoeD : (realSecond z : Circle) = second z := representative_coe _
  cases chores with
  | false =>
    simpa only [Fair, Bool.false_eq_true, ite_false, inputRows, hcoeC, hcoeD] using
      old_cake_failure_preserved A observer h (realFirst z) (realSecond z) hh hc0 hc1 hd0 hd1 hgap
  | true =>
    simpa only [Fair, ite_true, inputRows, hcoeC, hcoeD] using
      old_chore_failure_preserved A observer h (realFirst z) (realSecond z) hh hc0 hc1 hd0 hd1 hgap

/-- Pointwise retention for the real adaptive perturbation experiment.
Every old failure and every decoded uniform success remains an eventual
failure outside the actual detection, endpoint, old-gap and cap losses. -/
theorem actual_retained_failure {Tape : Type*} {n : ℕ} [NeZero n]
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag chores : Bool) (tape : Tape) (fuel : ℕ)
    (observer : Fin n) (z : ℝ × Circle) (h : ℝ) (hh : 0 < h)
    (hc0 : 0 < realFirst z - h / 2) (hc1 : realFirst z + h / 2 < 1)
    (hd0 : 0 < realSecond z - h / 2) (hd1 : realSecond z + h / 2 < 1)
    (hsafe : EndpointSafe h (realFirst z) (realSecond z)
      (determiningEndpoints uniform (run next (flaggedOracle flag uniform) tape fuel [])))
    (hmiss : (observer, z) ∉ NonnegativeDetection.detection
      (baselineRequests uniform (run next (flaggedOracle flag uniform) tape fuel [])))
    (hterminal : Terminal (run next (flaggedOracle flag uniform) tape fuel []).stop)
    (houtputSafe : ∀ A, (run next (flaggedOracle flag uniform) tape fuel []).stop = .returned A →
      SafeOutput A h (realFirst z) (realSecond z))
    (hgap : ∀ A, (run next (flaggedOracle flag uniform) tape fuel []).stop = .returned A →
      ¬ UniformEF A → h < uniformGap A)
    (hretain : ¬ Successful {A | UniformEF A} (run next (flaggedOracle flag uniform) tape fuel []) ∨
      ∃ A, (run next (flaggedOracle flag uniform) tape fuel []).stop = .returned A ∧
        UniformEF A ∧ Favorable chores A observer z) :
    tape ∉ eventualSuccess next (inputOracle flag h (observer, z)) []
      {A | Fair chores (inputRows h (observer, z)) A} := by
  have hreplay := actual_run_replay next flag tape fuel [] observer z h hh.le
    hc0 hc1 hd0 hd1 hsafe hmiss
  change run next (inputOracle flag h (observer, z)) tape fuel [] = _ at hreplay
  apply terminal_failure_no_eventual_success next (inputOracle flag h (observer, z)) tape []
    {A | Fair chores (inputRows h (observer, z)) A} fuel
  · simpa only [hreplay] using hterminal
  · rw [hreplay]
    rintro ⟨A, hreturned, hfair⟩
    rcases hretain with hold | ⟨B, hreturnedB, hB, hfavorable⟩
    · have hwrong : ¬ UniformEF A := fun hA => hold ⟨A, hreturned, hA⟩
      exact old_failure chores A observer z h hh.le hc0 hc1 hd0 hd1
        (hgap A hreturned hwrong) hfair
    · have hAB : A = B := Stop.returned.inj (hreturned.symm.trans hreturnedB)
      subst B
      exact decoded_failure chores A observer z h hh hc0 hc1 hd0 hd1
        (houtputSafe A hreturned) hB hfavorable hfair

end EnvyFreeResearch.Full.NonnegativeRetainedFailure

#print axioms EnvyFreeResearch.Full.NonnegativeRetainedFailure.decoded_failure
#print axioms EnvyFreeResearch.Full.NonnegativeRetainedFailure.actual_retained_failure
