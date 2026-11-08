import EnvyFreeResearch.Full.UpperRepairSeedIndices
import EnvyFreeResearch.Full.UpperCorrectionPaymentStates

/-! Pure full-buffer residue after the actual seed and payment selection.
The unchanged material outside the reserve is retained literally. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairRemaining

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperLogicalCells

variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

def remaining (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : State n) : State n :=
  UpperRepairResidue.finish (UpperGridData.aligned data) (UpperGridData.cuts data)
    (reserveCells (UpperGridData.parent data) theta labels)
    (UpperRepairSeedIndices.indices hk active origin data L theta labels pi threshold) final

theorem remaining_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : State n) :
    (remaining hk active origin data L theta labels pi threshold final).history = final.history := rfl

theorem remaining_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (data : X → UpperGridData.Data n coarse fine) (L : ℕ) (theta : I)
    (labels : X → Fin (coarse + 1) → I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1)) (final : X → State n)
    (horigin : Measurable origin) (hdata : Measurable data) (hlabels : ∀ c, Measurable (fun x => labels x c))
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (hfinal : Measurable final) :
    Measurable (fun x => remaining hk active (origin x) (data x) L theta (labels x) (pi x) (threshold x) (final x)) :=
  UpperRepairResidue.finish_measurable _ _ _ _ final
    (UpperGridData.aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))
    (reserveCells_measurable _ theta labels
      (UpperGridData.parent_measurable data hdata) hlabels)
    (UpperRepairSeedIndices.indices_measurable hk active origin data L theta labels pi threshold horigin hdata hlabels hpi hthreshold)
    hfinal

end EnvyFreeResearch.Full.UpperRepairRemaining
