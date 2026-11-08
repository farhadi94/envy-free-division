import EnvyFreeResearch.Full.UpperCorrectionProgram
import EnvyFreeResearch.Full.UpperProgramIteration
import EnvyFreeResearch.Full.UpperCorrectionLoop

/-! Ordinary-query compilation of the stopped correction loop. -/

noncomputable section

namespace EnvyFreeResearch.Full.UpperCorrectionLoopProgram

open UpperCircularStage UpperQueryPrograms UpperCorrectionLoop UpperProgramIteration Chores.QueryProgram

abbrev Circle := UpperCircular.Circle

variable {n m : ℕ}

def stepProgram (state : LoopState n) (draw : Job n × Circle) :
    QProgram n (Bool × LoopState n) :=
  if state.stopped then .returned (false, state) else
  (UpperCorrectionProgram.correction state.current draw.1.owner draw.1.deficit draw.2).bind (fun next =>
    if accepts draw.1 state.current next.2 then
      .returned (false, ⟨next.2, false, state.accepted ++ [next.1]⟩)
    else
      .returned (true, ⟨⟨state.current.cells, next.2.history⟩, true, state.accepted⟩))

def loopProgram (jobs : Fin m → Job n) (state : LoopState n) (tape : Fin m → Circle) :
    QProgram n ((Fin m → Bool) × LoopState n) :=
  runProgram stepProgram m state (fun i => (jobs i, tape i))

theorem stepProgram_executes (policy : Policy n) (state : LoopState n) (draw : Job n × Circle) :
    ∃ trace, Executes (totalPolicy policy) (stepProgram state draw) state.current.history
      (step policy state draw) trace ∧
      (step policy state draw).2.current.history = state.current.history ++ trace := by
  by_cases hs : state.stopped = true
  · refine ⟨[], ?_, ?_⟩
    · simpa only [stepProgram, step, hs, ite_true] using
        (Executes.returned (oracle := totalPolicy policy) (false, state) state.current.history)
    · simp [step, hs]
  · have hf : state.stopped = false := Bool.eq_false_iff.mpr hs
    obtain ⟨trace, hrun, heq⟩ := UpperCorrectionProgram.correction_executes policy
      state.current draw.1.owner draw.1.deficit draw.2
    refine ⟨trace, ?_, ?_⟩
    · let continuation (next : UpperDomainDifference.Correction × UpperCorrectionExecution.State n) :
          QProgram n (Bool × LoopState n) :=
        if accepts draw.1 state.current next.2 then
          Program.returned (false, ⟨next.2, false, state.accepted ++ [next.1]⟩)
        else
          Program.returned (true, ⟨⟨state.current.cells, next.2.history⟩, true, state.accepted⟩)
      have htail : Executes (totalPolicy policy)
          (continuation (UpperCorrectionExecution.execute policy state.current draw.1.owner draw.1.deficit draw.2))
          (state.current.history ++ trace) (step policy state draw) [] := by
        simp only [continuation, step, hf, Bool.false_eq_true, ite_false]
        split_ifs <;> exact Executes.returned _ _
      have h := hrun.bind continuation htail
      simpa only [stepProgram, continuation, hf, Bool.false_eq_true, ite_false, List.append_nil] using h
    · simp only [step, hf, Bool.false_eq_true, ite_false]
      split_ifs <;> exact heq

theorem loopProgram_executes (policy : Policy n) (jobs : Fin m → Job n)
    (state : LoopState n) (tape : Fin m → Circle) :
    ∃ trace, Executes (totalPolicy policy) (loopProgram jobs state tape) state.current.history
      (run policy jobs state tape) trace ∧
      (run policy jobs state tape).2.current.history = state.current.history ++ trace :=
  runProgram_executes policy (fun s : LoopState n => s.current.history) stepProgram (step policy)
    (stepProgram_executes policy) m state (fun i => (jobs i, tape i))

/-- Failed proposals and their observer evaluations remain in the compiled
trace; later stopped steps issue no queries. -/
theorem loopProgram_executes_bounded (policy : Policy n) (jobs : Fin m → Job n)
    (state : LoopState n) (tape : Fin m → Circle) :
    ∃ trace, Executes (totalPolicy policy) (loopProgram jobs state tape) state.current.history
      (run policy jobs state tape) trace ∧
      (run policy jobs state tape).2.current.history = state.current.history ++ trace ∧
      trace.length ≤ m * (2 * (n + 1)) ∧ (trace.map Prod.fst).countP isCut ≤ m * 2 := by
  obtain ⟨trace, hrun, heq⟩ := loopProgram_executes policy jobs state tape
  have hq := run_query_bound policy jobs state tape
  have hc := run_cut_bound policy jobs state tape
  rw [heq, List.length_append] at hq
  rw [heq, List.map_append, List.countP_append] at hc
  exact ⟨trace, hrun, heq, by omega, by omega⟩

end EnvyFreeResearch.Full.UpperCorrectionLoopProgram
