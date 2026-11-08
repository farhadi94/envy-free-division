import EnvyFreeResearch.Full.UpperShrinkRepair

/-! Sequential query accounting for deterministic carving followed by one
fresh actual Repair, including all rejected attempts. The carving execution
premise is to be discharged by the concrete refinement loop. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperRepairProgram
  Chores.QueryProgram

variable {n k : ℕ} [Nonempty (Fin k)]

def trialProgram (carve : QProgram n (Carved n k)) (hk : 2 ≤ k)
    (chores : Bool) (active : Fin k → Fin n) (p : UpperRepair.Tape n k) :
    QProgram n (PhysicalResult n k) :=
  carve.bind (fun out => UpperRepair.program hk chores active out.buffer out.old p)

theorem trial_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (carve : QProgram n (Carved n k)) (out : Carved n k)
    (trace : History n)
    (hcarve : Executes (totalPolicy policy) carve origin.history out trace)
    (hhistory : out.buffer.history = origin.history ++ trace)
    (hq : trace.length ≤ (n+1)*UpperRepair.fine n)
    (hc : (trace.map Prod.fst).countP isCut ≤ UpperRepair.fine n)
    (p : UpperRepair.Tape n k) :
    ∃ fullTrace, Executes (totalPolicy policy) (trialProgram carve hk chores active p) origin.history
      (UpperRepair.execute policy hk chores active out.buffer out.old p) fullTrace ∧
      (UpperRepair.execute policy hk chores active out.buffer out.old p).2.1.history = origin.history ++ fullTrace ∧
      fullTrace.length ≤ 8*n*UpperRepair.fine n ∧
      (fullTrace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n := by
  obtain ⟨rest, hr, hh, hqr, hcr⟩ := UpperRepair.program_cost policy hk chores active hinj out.buffer out.old p
  have hn : 1 ≤ n := by
    have hkn := Fintype.card_le_of_injective active hinj
    simp only [Fintype.card_fin] at hkn
    omega
  refine ⟨trace ++ rest, ?_, ?_, ?_, ?_⟩
  · exact hcarve.bind _ (hhistory ▸ hr)
  · rw [hh, hhistory, List.append_assoc]
  · rw [List.length_append]
    nlinarith
  · rw [List.map_append, List.countP_append]
    omega

end EnvyFreeResearch.Full.UpperShrink
