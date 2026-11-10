import EnvyFreeResearch.Full.RefinedUpperPreparationRetained
import EnvyFreeResearch.Full.RefinedUpperStabilityProcedure
import EnvyFreeResearch.Full.UpperLogicalIsolationPure

/-! Query-free deterministic preparation on the actual returned grid data. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperIdealPayments
open scoped Classical unitInterval
variable {n k coarse fine : ℕ}

def dataRun (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) :=
  RefinedUpperPeeling.run (UpperGridData.table active origin data) (UpperGridData.parent data)
    (List.ofFn (fun i : Fin (coarse+fine+1) => i)) (UpperLogicalIsolation.requests k L) ∅

def dataResult (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) := (dataRun active origin data L).getD ([],∅)

def dataRetained (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) : State n :=
  UpperGridData.reserve data 0 (retentionLabels (dataResult active origin data L).2)

def dataChosen (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) : Job k → Fin L → Fin (coarse+fine+1) :=
  UpperLogicalIsolation.coreChosen (UpperGridData.table active origin data)
    (UpperLogicalIsolation.multipliers active origin (dataRetained active origin data L)) (dataResult active origin data L).1 0

def dataWeights (active : Fin k → Fin n) (origin : State n) (data : UpperGridData.Data n coarse fine)
    (L : ℕ) : Job k → Fin L → Fin k → ℝ :=
  UpperLogicalIsolation.coreWeights (UpperGridData.table active origin data)
    (UpperLogicalIsolation.multipliers active origin (dataRetained active origin data L)) (dataResult active origin data L).1 0

def dataDisagreement (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) : Fin k → Fin k → ℝ :=
  UpperPayments.cellGap (UpperCorrectionSetup.table active (dataRetained active origin data L) (UpperGridData.cuts data))

def dataMatrix (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k-1+1) → Fin (L+1)) : Fin k → Fin k → ℝ :=
  UpperLogicalIsolation.coreMatrix hk (dataWeights active origin data L)
    (UpperLogicalIsolation.oldMatrix active old (dataRetained active origin data L)) pi threshold

lemma dataRetained_history (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) :
    (dataRetained active origin data L).history = data.2.2.history := rfl

lemma dataRun_execute (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) :
    dataRun active origin (UpperGridMerge.prepare policy active origin q m draw) L =
      RefinedUpperPeeling.representativeRun policy active origin q m draw (UpperLogicalIsolation.requests k L) := rfl

variable {X : Type*} [MeasurableSpace X]

lemma dataRun_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => dataRun active (origin x) (data x) L) :=
  RefinedUpperPeeling.table_run_measurable _ (UpperGridData.parent_measurable data hdata) _ _ _
    (UpperGridData.table_measurable active origin data horigin hdata) _ measurable_const

lemma dataResult_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => dataResult active (origin x) (data x) L) :=
  RefinedUpperPeeling.optionGetD_measurable _ (dataRun_measurable active origin data L horigin hdata) ([],∅)

lemma dataRetained_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => dataRetained active (origin x) (data x) L) := by
  apply UpperGridData.reserve_measurable _ 0 _ hdata
  intro p
  exact (measurable_of_countable (fun removed => retentionLabels removed p)).comp
    (measurable_snd.comp (dataResult_measurable active origin data L horigin hdata))

lemma dataChosen_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) (j : Job k) (a : Fin L) :
    Measurable (fun x => dataChosen active (origin x) (data x) L j a) := by
  apply UpperLogicalIsolation.coreChosen_measurable
  · exact UpperGridData.table_measurable active origin data horigin hdata
  · intro r
    exact (total_measurable origin _ horigin measurable_const).div
      (total_measurable _ _ (dataRetained_measurable active origin data L horigin hdata) measurable_const)
  · exact measurable_fst.comp (dataResult_measurable active origin data L horigin hdata)

lemma dataWeights_measurable (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) (j : Job k) (a : Fin L) (i : Fin k) :
    Measurable (fun x => dataWeights active (origin x) (data x) L j a i) := by
  apply UpperLogicalIsolation.coreWeights_measurable
  · exact UpperGridData.table_measurable active origin data horigin hdata
  · intro r
    exact (total_measurable origin _ horigin measurable_const).div
      (total_measurable _ _ (dataRetained_measurable active origin data L horigin hdata) measurable_const)
  · exact measurable_fst.comp (dataResult_measurable active origin data L horigin hdata)

lemma dataMatrix_measurable (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : X → State n)
    (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : X → Equiv.Perm (Fin k)) (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (horigin : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c)) (hdata : Measurable data)
    (hpi : Measurable pi) (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (i c : Fin k) :
    Measurable (fun x => dataMatrix hk active (origin x) (old x) (data x) L (pi x) (threshold x) i c) :=
  UpperLogicalIsolation.coreMatrix_measurable hk _ _ pi threshold
    (dataWeights_measurable active origin data L horigin hdata)
    (UpperLogicalIsolation.oldMatrix_measurable active old _ hold (dataRetained_measurable active origin data L horigin hdata))
    hpi hthreshold i c

end EnvyFreeResearch.Full.RefinedUpperPreparation
