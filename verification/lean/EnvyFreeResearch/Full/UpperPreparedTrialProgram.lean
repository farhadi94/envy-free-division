import EnvyFreeResearch.Full.UpperGridData
import EnvyFreeResearch.Full.UpperCorrectionStageProgram

/-! One ordinary-query grid/preparation/correction trial. Post-grid target
and acceptance computations are pure functions of returned cached data.
Every rejection restores the input physical buffer while keeping all new
answers. This compiler theorem does not assume the pure preparation succeeds. -/

noncomputable section

open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperPreparedTrialProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQueryPrograms
  UpperGridData UpperCorrectionStageProgram Chores.QueryProgram

variable {n k q m : ℕ} [Nonempty (Fin k)]

abbrev Grid (n k q m : ℕ) := Data n (UpperRecordedQuantiles.count (Agent := Fin k) q) m
abbrev Result (n k q m : ℕ) := Grid n k q m × UpperCorrectionStageProgram.Result n k

def rollback (origin : State n) (result : UpperCorrectionStageProgram.Result n k) :
    UpperCorrectionStageProgram.Result n k :=
  if result.2.2 then ((fun _ => []), ⟨origin.cells, result.2.1.history⟩, true) else result

theorem rollback_history (origin : State n) (result : UpperCorrectionStageProgram.Result n k) :
    (rollback origin result).2.1.history = result.2.1.history := by
  unfold rollback
  split_ifs <;> rfl

theorem rollback_rejected (origin : State n) (result : UpperCorrectionStageProgram.Result n k)
    (h : result.2.2 = true) : (rollback origin result).1 = (fun _ => []) ∧
      (rollback origin result).2.1.cells = origin.cells ∧ (rollback origin result).2.2 = true := by
  simp [rollback, h]

def continuation (active : Fin k → Fin n) (origin : State n) (data : Grid n k q m)
    (theta : I) (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) : QProgram n (Result n k q m) :=
  if approved data then
    (UpperCorrectionStageProgram.program active (reserve data theta labels) (cuts data)
      (targets data) eta lam starts).bind (fun result => .returned (data, rollback origin result))
  else .returned (data, (fun _ => []), ⟨origin.cells, data.2.2.history⟩, true)

def program (active : Fin k → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) : QProgram n (Result n k q m) :=
  (UpperRecordedGridProgram.prepare active origin q m draw).bind (fun data =>
    continuation active origin data theta labels eta lam targets approved starts)

def afterGrid (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (data : Grid n k q m)
    (theta : I) (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) : Result n k q m :=
  if approved data then
    (data, rollback origin (executeStage policy active (reserve data theta labels) (cuts data) (targets data) eta lam starts))
  else (data, (fun _ => []), ⟨origin.cells, data.2.2.history⟩, true)

def executeTrial (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) : Result n k q m :=
  afterGrid policy active origin (UpperGridMerge.prepare policy active origin q m draw)
    theta labels eta lam targets approved starts

theorem continuation_executes (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (data : Grid n k q m)
    (theta : I) (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (continuation active origin data theta labels eta lam targets approved starts)
      data.2.2.history (afterGrid policy active origin data theta labels eta lam targets approved starts) trace ∧
      (afterGrid policy active origin data theta labels eta lam targets approved starts).2.2.1.history = data.2.2.history ++ trace ∧
      trace.length ≤ k * (2 * (n + 1)) ∧ (trace.map Prod.fst).countP isCut ≤ 2 * k := by
  by_cases h : approved data = true
  · obtain ⟨trace, hrun, heq, hq, hc⟩ := program_executes policy active (reserve data theta labels)
      (cuts data) (targets data) eta lam starts
    have hhistory : (reserve data theta labels).history = data.2.2.history := rfl
    refine ⟨trace, ?_, ?_, hq, by simpa only [Nat.mul_comm] using hc⟩
    · have ht := hrun.bind (fun result => Program.returned (data, rollback origin result))
        (Executes.returned (data, rollback origin (executeStage policy active (reserve data theta labels)
          (cuts data) (targets data) eta lam starts)) (data.2.2.history ++ trace))
      simpa only [continuation, afterGrid, h, ite_true, List.append_nil, hhistory] using ht
    · simpa only [afterGrid, h, ite_true, rollback_history, hhistory] using heq
  · refine ⟨[], ?_, by simp [afterGrid, h], by simp, by simp⟩
    simpa only [continuation, afterGrid, h, Bool.false_eq_true, ite_false] using
      (Executes.returned (oracle := totalPolicy policy)
        (afterGrid policy active origin data theta labels eta lam targets approved starts) data.2.2.history)

/-- The exact returned trace includes initialization of the common grid and
the first rejected correction, and failed preparation makes no correction calls. -/
theorem program_executes (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (program active origin q m draw theta labels eta lam targets approved starts)
      origin.history (executeTrial policy active origin q m draw theta labels eta lam targets approved starts) trace ∧
      (executeTrial policy active origin q m draw theta labels eta lam targets approved starts).2.2.1.history = origin.history ++ trace ∧
      trace.length ≤ (k * q + m) * (n + 1) + k * (2 * (n + 1)) ∧
      (trace.map Prod.fst).countP isCut ≤ k * q + m + 2 * k := by
  obtain ⟨gridTrace, hgrid, hgridEq⟩ := UpperRecordedGridProgram.prepare_executes policy active origin q m draw
  obtain ⟨lastTrace, hlast, hlastEq, hlastQ, hlastC⟩ := continuation_executes policy active origin
    (UpperGridMerge.prepare policy active origin q m draw) theta labels eta lam targets approved starts
  have hlast' : Executes (totalPolicy policy)
      (continuation active origin (UpperGridMerge.prepare policy active origin q m draw) theta labels eta lam targets approved starts)
      (origin.history ++ gridTrace)
      (executeTrial policy active origin q m draw theta labels eta lam targets approved starts) lastTrace := by
    rw [← hgridEq]
    exact hlast
  have hq := UpperGridMerge.query_bound policy active origin q m draw
  have hc := UpperGridMerge.cut_bound policy active origin q m draw
  simp only [Fintype.card_fin, hgridEq, List.length_append] at hq
  simp only [Fintype.card_fin, hgridEq, List.map_append, List.countP_append] at hc
  refine ⟨gridTrace ++ lastTrace, hgrid.bind _ hlast', ?_, ?_, ?_⟩
  · change (afterGrid policy active origin _ theta labels eta lam targets approved starts).2.2.1.history = _
    rw [hlastEq, hgridEq, List.append_assoc]
  · rw [List.length_append]
    omega
  · rw [List.map_append, List.countP_append]
    omega

end EnvyFreeResearch.Full.UpperPreparedTrialProgram
