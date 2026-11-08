import EnvyFreeResearch.Full.UpperSnapshotCandidatesPartition
import EnvyFreeResearch.Full.UpperSnapshotCandidatesSelect

/-! The large branch factors through pure returned GridData and its cached
table. These definitions never invoke the oracle response policy. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation
variable {n k coarse fine : ℕ}

def candidatePositive (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) : Fin (coarse + fine + 1) :=
  selectedPositive hk (UpperGridData.table active origin data) cutter

def candidateNegative (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) : Fin (coarse + fine + 1) :=
  selectedNegative hk (UpperGridData.table active origin data) cutter

def candidateOld (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) (j : Fin k) : State n :=
  largeEndowment (UpperGridData.aligned data) (UpperGridData.cuts data)
    (candidatePositive hk active origin data cutter) (candidateNegative hk active origin data cutter) j

def candidateBuffer (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) : State n :=
  largeBuffer (UpperGridData.aligned data) (UpperGridData.cuts data)
    (candidatePositive hk active origin data cutter) (candidateNegative hk active origin data cutter)

theorem candidateOld_history (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter j : Fin k) :
    (candidateOld hk active origin data cutter j).history = data.2.2.history := by
  rw [candidateOld, largeEndowment_history]
  rfl

theorem candidateBuffer_history (hk : 0 < k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) :
    (candidateBuffer hk active origin data cutter).history = data.2.2.history := rfl

variable {X : Type*} [MeasurableSpace X]

theorem candidatePositive_measurable (hk : 0 < k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (cutter : Fin k) (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => candidatePositive hk active (origin x) (data x) cutter) :=
  selectedPositive_measurable hk _ cutter (UpperGridData.table_measurable active origin data horigin hdata)

theorem candidateNegative_measurable (hk : 0 < k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (cutter : Fin k) (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => candidateNegative hk active (origin x) (data x) cutter) :=
  selectedNegative_measurable hk _ cutter (UpperGridData.table_measurable active origin data horigin hdata)

theorem candidateOld_measurable (hk : 0 < k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (cutter j : Fin k) (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => candidateOld hk active (origin x) (data x) cutter j) :=
  largeEndowment_measurable _ _ _ _ (UpperGridData.aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))
    (candidatePositive_measurable hk active origin data cutter horigin hdata)
    (candidateNegative_measurable hk active origin data cutter horigin hdata) j

theorem candidateBuffer_measurable (hk : 0 < k) (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (cutter : Fin k) (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => candidateBuffer hk active (origin x) (data x) cutter) :=
  largeBuffer_measurable _ _ _ _ (UpperGridData.aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))
    (candidatePositive_measurable hk active origin data cutter horigin hdata)
    (candidateNegative_measurable hk active origin data cutter horigin hdata)

end EnvyFreeResearch.Full.UpperSnapshotCandidates
