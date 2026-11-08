import EnvyFreeResearch.Full.UpperQueryPrograms
import EnvyFreeResearch.Full.UpperFreshSamples

/-! Finite iteration of actual ordinary-query programs with full traces. -/

noncomputable section

namespace EnvyFreeResearch.Full.UpperProgramIteration

open UpperCircularStage UpperQueryPrograms Chores.QueryProgram

variable {n : ℕ} {State Draw Sample : Type*}

def runProgram (step : State → Draw → QProgram n (Sample × State)) :
    (m : ℕ) → State → (Fin m → Draw) → QProgram n ((Fin m → Sample) × State)
  | 0, state, _ => .returned (Fin.elim0, state)
  | m + 1, state, draw => (step state (draw 0)).bind (fun first =>
      (runProgram step m first.2 (fun i => draw i.succ)).bind (fun rest =>
        .returned (Fin.cons first.1 rest.1, rest.2)))

/-- Operational composition is proved against the actual full-history policy;
no query is dropped when the finite stage changes its internal state. -/
theorem runProgram_executes (policy : Policy n) (historyOf : State → History n)
    (program : State → Draw → QProgram n (Sample × State))
    (step : State → Draw → Sample × State)
    (hstep : ∀ state draw, ∃ trace,
      Executes (totalPolicy policy) (program state draw) (historyOf state) (step state draw) trace ∧
      historyOf (step state draw).2 = historyOf state ++ trace)
    (m : ℕ) (state : State) (draw : Fin m → Draw) :
    ∃ trace, Executes (totalPolicy policy) (runProgram program m state draw) (historyOf state)
      (UpperFreshSamples.run step m state draw) trace ∧
      historyOf (UpperFreshSamples.run step m state draw).2 = historyOf state ++ trace := by
  induction m generalizing state with
  | zero => exact ⟨[], Executes.returned _ _, by simp [UpperFreshSamples.run]⟩
  | succ m ih =>
    obtain ⟨firstTrace, hfirst, hfirstEq⟩ := hstep state (draw 0)
    obtain ⟨restTrace, hrest, hrestEq⟩ := ih (step state (draw 0)).2 (fun i => draw i.succ)
    have htail := hrest.bind (fun rest : (Fin m → Sample) × State => Program.returned
        (Fin.cons (α := fun _ : Fin (m + 1) => Sample) (step state (draw 0)).1 rest.1, rest.2))
      (Executes.returned (UpperFreshSamples.run step (m + 1) state draw)
        (historyOf (step state (draw 0)).2 ++ restTrace))
    have htail' : Executes (totalPolicy policy)
        ((runProgram program m (step state (draw 0)).2 (fun i => draw i.succ)).bind
          (fun rest : (Fin m → Sample) × State => .returned
            (Fin.cons (α := fun _ : Fin (m + 1) => Sample) (step state (draw 0)).1 rest.1, rest.2)))
        (historyOf state ++ firstTrace) (UpperFreshSamples.run step (m + 1) state draw) restTrace := by
      rw [← hfirstEq]
      simpa only [List.append_nil] using htail
    refine ⟨firstTrace ++ restTrace, hfirst.bind _ htail', ?_⟩
    change historyOf (UpperFreshSamples.run step m (step state (draw 0)).2 (fun i => draw i.succ)).2 = _
    rw [hrestEq, hfirstEq, List.append_assoc]

end EnvyFreeResearch.Full.UpperProgramIteration
