import EnvyFreeResearch.Full.UpperPreparedTrialProgram

/-! Pathwise ordinary-query accounting for the complete compiled trial,
including every preparation rejection and every failed correction attempt. -/

noncomputable section

open scoped unitInterval

namespace EnvyFreeResearch.Full.UpperPreparedTrialCost

open Chores.QueryProgram UpperPreparedTrialProgram UpperQueryPrograms UpperCircularStage
  UpperCorrectionExecution

variable {n k : ℕ} [Nonempty (Fin k)]

theorem raw_trial_bounds (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Fin k × I) (theta : I)
    (labels : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I)
    (eta lam : ℝ) (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle) (hn : 1 ≤ n) (hcoarse : k * q ≤ m) (hcorrections : 2 * k ≤ m) :
    ∃ trace, Executes (totalPolicy policy)
      (program active origin q m draw theta labels eta lam targets approved starts) origin.history
      (executeTrial policy active origin q m draw theta labels eta lam targets approved starts) trace ∧
      (executeTrial policy active origin q m draw theta labels eta lam targets approved starts).2.2.1.history =
        origin.history ++ trace ∧ trace.length ≤ 6 * n * m ∧ (trace.map Prod.fst).countP isCut ≤ 3 * m := by
  obtain ⟨trace, hexec, hhistory, hq, hc⟩ := UpperPreparedTrialProgram.program_executes
    policy active origin q m draw theta labels eta lam targets approved starts
  have h3 : k * q + m + 2 * k ≤ 3 * m := by omega
  refine ⟨trace, hexec, hhistory, ?_, hc.trans h3⟩
  calc
    trace.length ≤ (k * q + m) * (n + 1) + k * (2 * (n + 1)) := hq
    _ = (k * q + m + 2 * k) * (n + 1) := by ring
    _ ≤ (3 * m) * (n + 1) := Nat.mul_le_mul_right _ h3
    _ ≤ (3 * m) * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    _ = 6 * n * m := by ring

end EnvyFreeResearch.Full.UpperPreparedTrialCost
