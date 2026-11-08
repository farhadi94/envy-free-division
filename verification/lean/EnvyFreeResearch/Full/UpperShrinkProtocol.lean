import EnvyFreeResearch.Full.UpperShrinkCarvingProgram
import EnvyFreeResearch.Full.UpperShrinkTrial

/-! One actual prescribed Shrink attempt: deterministic multicolor carving,
then an independently sampled Repair. The query bound includes rejected calls. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms UpperRepairProgram Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (G : ℝ) (p : UpperRepair.Tape n k) : QProgram n (PhysicalResult n k) :=
  trialProgram (carvingProgram active origin G) hk chores active p

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (G : ℝ) (p : UpperRepair.Tape n k) : PhysicalResult n k :=
  let carved := carvingExecute policy active origin G
  UpperRepair.execute policy hk chores active carved.buffer carved.old p

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (G : ℝ) (hG : 1 ≤ G) (p : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin G p) origin.history
      (execute policy hk chores active origin G p) trace ∧
      (execute policy hk chores active origin G p).2.1.history=origin.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  obtain ⟨tr,he,hh,hq,hc⟩ := carving_cost policy active origin (by omega) hkn G hG
  exact trial_cost policy hk chores active hinj origin (carvingProgram active origin G)
    (carvingExecute policy active origin G) tr he hh hq hc p

end EnvyFreeResearch.Full.UpperShrink
