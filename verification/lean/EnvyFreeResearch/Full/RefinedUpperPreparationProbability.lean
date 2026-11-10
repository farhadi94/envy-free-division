import EnvyFreeResearch.Full.RefinedUpperPreparationWeights
import EnvyFreeResearch.Full.UpperLogicalIsolationProbability

/-! Fresh finite permutation and threshold isolation for the actual new grid. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperRecordedQuantiles UpperLogicalIsolation Chores
open scoped Classical unitInterval ENNReal
variable {n k : ℕ} [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

/-- This is uniform over the full realized grid, so subsequent averaging
preserves the iid grid law without conditioning on any preparation event. -/
theorem data_cycle_probability (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) (old : Fin k → State n)
    (lam : ℝ) (hlam : 0 ≤ lam) (chores : Bool) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    isolationLaw k L {t | cycleReject chores
      (dataMatrix hk active origin old data L t.1 t.2)
      (dataDisagreement active origin data L) lam = true} ≤
      ENNReal.ofReal (isolationBound k L lam) := by
  dsimp only
  apply core_cycle_probability hk _ _ _
    (fun i j => UpperPayments.cellGap_nonneg _ i j)
    (fun i j => UpperPayments.cellGap_symmetric _ i j) lam hlam _ chores
  intro j a
  have h := dataWeights_gap μ policy hpolicy active origin hgood hpositive q m L draw hbudget j a
  have hn := UpperPayments.cellGap_nonneg
    (UpperCorrectionSetup.table active
      (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L)
      (UpperGridData.cuts (UpperGridMerge.prepare policy active origin q m draw))) j.1.1.1 j.1.1.2
  change 0 ≤ dataDisagreement active origin (UpperGridMerge.prepare policy active origin q m draw) L _ _ at hn
  dsimp only [dataDisagreement] at h hn
  linarith

omit [Nonempty (Fin k)] hpolicy hgood hpositive in
lemma dataDisagreement_measurable {X : Type*} [MeasurableSpace X] {coarse fine : ℕ}
    (active : Fin k → Fin n) (origin : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (L : ℕ)
    (horigin : Measurable origin) (hdata : Measurable data) (i j : Fin k) :
    Measurable (fun x => dataDisagreement active (origin x) (data x) L i j) :=
  UpperPayments.cellGap_measurable _ (UpperCorrectionSetup.table_measurable active _ _
    (dataRetained_measurable active origin data L horigin hdata)
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata))) i j

end EnvyFreeResearch.Full.RefinedUpperPreparation
