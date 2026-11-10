import EnvyFreeResearch.Full.RefinedUpperRepairTargets
import EnvyFreeResearch.Full.RefinedUpperRepairBatchCertified
import EnvyFreeResearch.Full.RefinedUpperCorrectionOutputMeasurable

/-! Actual ordinary-query preparation followed by bounded physical correction
retries. Failed finite cycle isolation performs no correction queries. Every
query from failed correction attempts remains in the returned transcript. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairTrial
open UpperRecordedDomain UpperCorrectionExecution UpperCorrectionLoop UpperCircularStage UpperStageMeasurable
  UpperRepairJobs UpperQueryPrograms Chores.QueryProgram ProgramMeasurable RefinedUpperPreparationProgram
  RefinedUpperRepairTargets RefinedUpperCorrectionSetup
variable {n k coarse fine r : ℕ} [Nonempty (Fin k)]

abbrev Result (n k coarse fine : ℕ) := Prepared n k coarse fine × LoopState n

def rejected (origin : State n) (p : Prepared n k coarse fine) : LoopState n :=
  ⟨⟨origin.cells,p.2.1.history⟩,true,[]⟩

def continuation (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (p : Prepared n k coarse fine) (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    QProgram n (Result n k coarse fine) :=
  if approved chores active p lam then
    (RefinedUpperBatchLoop.program
      (tasks active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta lam)
      (startState active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta) tape).bind
      (fun result => .returned (p,result.2))
  else .returned (p,rejected origin p)

def after (policy : Policy n) (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (p : Prepared n k coarse fine) (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) : Result n k coarse fine :=
  if approved chores active p lam then
    (p,(RefinedUpperBatchLoop.run policy
      (tasks active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta lam)
      (startState active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta) tape).2)
  else (p,rejected origin p)

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    QProgram n (Result n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m) :=
  (RefinedUpperPreparationProgram.program hk chores active origin old q m L draw pi threshold).bind
    (fun p => continuation chores active origin p eta lam tape)

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    Result n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m :=
  after policy chores active origin
    (RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L draw pi threshold) eta lam tape

theorem continuation_cost (policy : Policy n) (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (p : Prepared n k coarse fine) (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (continuation chores active origin p eta lam tape)
      p.2.1.history (after policy chores active origin p eta lam tape) trace ∧
      (after policy chores active origin p eta lam tape).2.current.history = p.2.1.history ++ trace ∧
      trace.length ≤ k*(r*(2*(n+1))) ∧ (trace.map Prod.fst).countP isCut ≤ k*(r*2) := by
  by_cases ha : approved chores active p lam = true
  · obtain ⟨trace,he,hh,hq,hc⟩ := RefinedUpperBatchLoop.program_executes_bounded policy
      (tasks active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta lam)
      (startState active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta) tape
    refine ⟨trace,?_,?_,hq,hc⟩
    · have h := he.bind (fun result => Chores.QueryProgram.Program.returned (p,result.2))
        (Executes.returned _ _)
      simpa only [continuation,after,ha,ite_true,List.append_nil,startState,initial,UpperPendingExclusion.remove] using h
    · simpa only [after,ha,ite_true,startState,initial,UpperPendingExclusion.remove] using hh
  · refine ⟨[],?_,?_,by simp,by simp⟩
    · simpa only [continuation,after,ha,Bool.false_eq_true,ite_false] using
        (Executes.returned (oracle := totalPolicy policy) (p,rejected origin p) p.2.1.history)
    · simp [after,ha,rejected]

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L draw pi threshold eta lam tape)
      origin.history (execute policy hk chores active origin old q m L draw pi threshold eta lam tape) trace ∧
      (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.current.history = origin.history ++ trace ∧
      trace.length ≤ (k*q+m)*(n+1)+k*(r*(2*(n+1))) ∧
      (trace.map Prod.fst).countP isCut ≤ k*q+m+k*(r*2) := by
  obtain ⟨first,hf,hfh,hfq,hfc⟩ := RefinedUpperPreparationProgram.program_cost policy hk chores active origin old q m L draw pi threshold
  obtain ⟨last,hl,hlh,hlq,hlc⟩ := continuation_cost policy chores active origin
    (RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L draw pi threshold) eta lam tape
  have hl' : Executes (totalPolicy policy)
      (continuation chores active origin
        (RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L draw pi threshold) eta lam tape)
      (origin.history ++ first) (execute policy hk chores active origin old q m L draw pi threshold eta lam tape) last := by
    rw [← hfh]
    exact hl
  refine ⟨first++last,hf.bind _ hl',?_,?_,?_⟩
  · change (after policy chores active origin _ eta lam tape).2.current.history = _
    rw [hlh,hfh,List.append_assoc]
  · simp only [List.length_append]
    omega
  · simp only [List.map_append,List.countP_append]
    omega

end EnvyFreeResearch.Full.RefinedUpperRepairTrial
