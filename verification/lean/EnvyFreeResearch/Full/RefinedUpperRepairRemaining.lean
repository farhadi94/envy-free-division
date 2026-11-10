import EnvyFreeResearch.Full.RefinedUpperRepairSeedIndices
import EnvyFreeResearch.Full.UpperCorrectionPaymentStates

/-! Pure full-buffer residue after the actual seed and payment selection.
The unchanged material outside the reserve is retained literally. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairRemaining

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperPreparation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperLogicalCells

variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

def remaining (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : State n) : State n :=
  UpperRepairResidue.finish (UpperGridData.aligned data) (UpperGridData.cuts data)
    (RefinedUpperRepairSeedIndices.reserved active origin data L)
    (RefinedUpperRepairSeedIndices.indices hk active origin data L pi threshold) final

theorem remaining_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : State n) :
    (remaining hk active origin data L pi threshold final).history = final.history := rfl

theorem remaining_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : X → State n)
    (horigin : Measurable origin) (hdata : Measurable data)
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (hfinal : Measurable final) :
    Measurable (fun x => remaining hk active (origin x) (data x) L (pi x) (threshold x) (final x)) :=
  UpperRepairResidue.finish_measurable _ _ _ _ final
    (UpperGridData.aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))
    (RefinedUpperRepairSeedIndices.reserved_measurable active origin data L horigin hdata)
    (RefinedUpperRepairSeedIndices.indices_measurable hk active origin data L pi threshold horigin hdata hpi hthreshold)
    hfinal

end EnvyFreeResearch.Full.RefinedUpperRepairRemaining
