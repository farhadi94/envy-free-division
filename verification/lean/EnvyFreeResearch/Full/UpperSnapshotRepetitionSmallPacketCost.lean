import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotRepetitionPacket
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperQueryPrograms Chores.QueryProgram
variable {n m J : ℕ}

theorem actual_small_packet_cost (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ)
    (check : State n → Circle × Circle → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Bool)
    (origin : State n) (tape : Tape (Circle × Circle) (16*J)) :
    ∃ trace, Executes (totalPolicy policy)
      (program (packetAttempt (smallAttempt cutter cuts selected t check)) (drawList tape) origin) origin.history
      (run (packetStep (smallStep policy cutter cuts selected t check)) (drawList tape) origin) trace ∧
      (run (packetStep (smallStep policy cutter cuts selected t check)) (drawList tape) origin).1.history=origin.history++trace ∧
      trace.length ≤ (16*J)*((J+2)*(n+1)) ∧
      (trace.map Prod.fst).countP isCut ≤ (16*J)*(J+2) := by
  have hstep (state : State n) (z : Circle × Circle) :
      ∃ trace, Executes (totalPolicy policy)
        (packetAttempt (smallAttempt cutter cuts selected t check) state z) state.history
        (packetStep (smallStep policy cutter cuts selected t check) state z) trace ∧
        (packetStep (smallStep policy cutter cuts selected t check) state z).1.history = state.history ++ trace ∧
        trace.length ≤ (J+2)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ J+2 := by
    obtain ⟨trace,he,hh,hq,hc⟩ := small_attempt_cost policy cutter cuts selected t check state z
    exact ⟨trace,packet_attempt_executes (totalPolicy policy) State.history
      (smallStep policy cutter cuts selected t check) (smallAttempt cutter cuts selected t check) state z trace he,
      hh,hq,hc⟩
  simpa only [drawList_length] using program_executes (totalPolicy policy) State.history
    (packetStep (smallStep policy cutter cuts selected t check))
    (packetAttempt (smallAttempt cutter cuts selected t check)) isCut
    ((J+2)*(n+1)) (J+2) hstep (drawList tape) origin

end EnvyFreeResearch.Full.UpperSnapshotRepetition
