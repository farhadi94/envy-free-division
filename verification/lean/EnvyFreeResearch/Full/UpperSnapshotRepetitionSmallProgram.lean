import EnvyFreeResearch.Full.UpperSnapshotRepetitionBridge
import EnvyFreeResearch.Full.UpperSnapshotSmallProgramPost
import EnvyFreeResearch.Full.UpperSnapshotSmallProgramRestored

/-! Actual first-accepting repeated two-circle programs. Both accepted and
rejected attempts retain every queried endpoint in the full restored state. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperQueryPrograms Chores.QueryProgram
abbrev Circle := UpperCircular.Circle
variable {n m J : ℕ}

abbrev SmallRaw (n J : ℕ) := ((Fin 2 → ℝ) × State n) × ((Fin J → ℝ) × State n)

def smallPost (origin : State n)
    (check : ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (first : (Fin 2 → ℝ) × State n) (second : (Fin J → ℝ) × State n) :
    State n × Option (SmallRaw n J) :=
  (secondRestoredFrom origin first second,if check first second then some (first,second) else none)

def smallAttempt (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (z : Circle × Circle) : QProgram n (State n × Option (SmallRaw n J)) :=
  twoStageProgram origin cutter cuts selected t z.1 z.2 (smallPost origin (check origin z))

def smallStep (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (z : Circle × Circle) : State n × Option (SmallRaw n J) :=
  smallPost origin (check origin z) (firstRun policy origin cutter cuts selected t z.1)
    (secondRun (J:=J) policy origin cutter cuts selected t z.1 z.2)

theorem small_attempt_cost (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (z : Circle × Circle) :
    ∃ trace, Executes (totalPolicy policy) (smallAttempt cutter cuts selected t check origin z)
      origin.history (smallStep policy cutter cuts selected t check origin z) trace ∧
      (smallStep policy cutter cuts selected t check origin z).1.history=origin.history++trace ∧
      trace.length ≤ (J+2)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J+2 :=
  two_stage_program_cost policy origin cutter cuts selected t z.1 z.2 (smallPost origin (check origin z))

theorem small_repeated_cost (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (tape : Tape (Circle × Circle) (16*J)) :
    ∃ trace, Executes (totalPolicy policy)
      (program (smallAttempt cutter cuts selected t check) (drawList tape) origin) origin.history
      (run (smallStep policy cutter cuts selected t check) (drawList tape) origin) trace ∧
      (run (smallStep policy cutter cuts selected t check) (drawList tape) origin).1.history=origin.history++trace ∧
      trace.length ≤ (16*J)*((J+2)*(n+1)) ∧
      (trace.map Prod.fst).countP isCut ≤ (16*J)*(J+2) := by
  simpa only [drawList_length] using program_executes (totalPolicy policy) State.history
    (smallStep policy cutter cuts selected t check) (smallAttempt cutter cuts selected t check) isCut
    ((J+2)*(n+1)) (J+2) (small_attempt_cost policy cutter cuts selected t check) (drawList tape) origin

end EnvyFreeResearch.Full.UpperSnapshotRepetition
