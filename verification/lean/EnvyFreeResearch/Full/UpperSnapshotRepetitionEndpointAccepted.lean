import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointVector
import EnvyFreeResearch.Full.UpperSnapshotRepetitionPacket

noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
variable {State Draw Output : Type} {L : ℕ}

theorem packet_endpoint_mem (step : State → Draw → State × Option Output)
    (points : State → Draw → Fin L → ℝ) (m : ℕ) (s : State) (tape : Tape Draw m)
    (p : Packet State Draw Output)
    (hp : (run (packetStep step) (drawList tape) s).2=some p) (j : Fin L) :
    points p.1 p.2.1 j ∈ endpoints (fun s d => (step s d).1)
      (fun s d => (step s d).2.isNone) points m s tape := by
  induction m generalizing s with
  | zero => simp [drawList,run] at hp
  | succ m ih =>
    cases ho : (step s tape.1).2 with
    | none =>
      have hrec := ih (step s tape.1).1 tape.2
        (by simpa only [drawList,run,packetStep,ho,Option.map_none] using hp)
      simp only [endpoints,ho,Option.isNone_none,ite_true]
      exact List.mem_append_right _ hrec
    | some a =>
      have heq : (s,tape.1,a)=p := by
        simpa only [drawList,run,packetStep,ho,Option.map_some,Option.some.injEq] using hp
      subst p
      simp only [endpoints,ho,Option.isNone_some,Bool.false_eq_true,ite_false]
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem packet_endpoint_supported (step : State → Draw → State × Option Output)
    (points : State → Draw → Fin L → ℝ) (m : ℕ) (s : State) (tape : Tape Draw m)
    (p : Packet State Draw Output)
    (hp : (run (packetStep step) (drawList tape) s).2=some p) (j : Fin L) :
    ∃ e, endpointVector (fun s d => (step s d).1) (fun s d => (step s d).2.isNone)
      points m s tape e = points p.1 p.2.1 j := by
  have h := packet_endpoint_mem step points m s tape p hp j
  rw [← endpointVector_ofFn] at h
  exact List.mem_ofFn.mp h

end EnvyFreeResearch.Full.UpperSnapshotRepetition
