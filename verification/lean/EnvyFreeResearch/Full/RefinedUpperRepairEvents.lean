import EnvyFreeResearch.Full.RefinedUpperRepairOutputMeasurable
import EnvyFreeResearch.Full.RefinedUpperActualBadGrid
import EnvyFreeResearch.Full.RefinedUpperActualCorrectionBound

/-! Measurable failure events on the original Repair tape. The exceptional
grid is an analytic event, not a query or an additional rejection guard. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepairEvents
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperRepairLaw RefinedUpperStability RefinedUpperPreparation
variable {n k m L r : ℕ} [Nonempty (Fin k)]

def prepared (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (x : Parameter k m L) :=
  RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L x.1 x.2.1 x.2.2

def badGrid (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Fin k → Fin n)
    (origin : State n) (q : ℕ) (δ : ℝ) : Set (Parameter k m L) :=
  {x | δ ≤ (UpperMixtureSampling.mixture μ active origin.cells).real
    (physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L)
      (RefinedUpperActualCorrectionBound.finalJobs k)
      (UpperGridMerge.prepare policy active origin q m x.1).1
      (UpperGridMerge.prepare policy active origin q m x.1).2.1)}

def badCycle (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (lam : ℝ) : Set (Parameter k m L) :=
  {x | RefinedUpperRepairTargets.approved chores active (prepared policy hk chores active origin old q x) lam = false}

def failed (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (eta lam : ℝ) : Set (Tape k m L r) :=
  {x | (execute policy hk chores active origin old q eta lam x).2.2 = true}

theorem prepared_measurable (policy : Policy n) (hm : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) :
    Measurable (prepared (m := m) (L := L) policy hk chores active origin old q) :=
  RefinedUpperPreparationProgram.finish_measurable hk chores active (fun _ => origin) (fun _ => old)
    (UpperRepairTrialLaw.data policy active origin q) L (fun x => x.2.1) (fun x => x.2.2)
    measurable_const (fun _ => measurable_const) (UpperRepairTrialLaw.data_measurable policy hm active origin q)
    (measurable_fst.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

theorem badGrid_measurable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (policy : Policy n) (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (origin : State n) (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q : ℕ) (δ : ℝ) :
    MeasurableSet (badGrid (m := m) (L := L) μ policy active origin q δ) := by
  letI := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  have hmass := protectedMass_measurable (m := m)
    (RefinedUpperPeeling.endpointProcedure (RefinedUpperPeeling.physicalCumulative μ active origin)
      (UpperRecordedQuantiles.cuts policy active origin q) (UpperLogicalIsolation.requests k L)
      (RefinedUpperActualCorrectionBound.finalJobs k))
    (RefinedUpperPeeling.endpointProcedure_measurable _
      (RefinedUpperPeeling.physicalCumulative_measurable μ active origin) _ _ _)
    (UpperRecordedQuantiles.run policy active origin q).1
    (UpperMixtureSampling.mixture μ active origin.cells)
  have hsamples := measurable_fst.comp (measurable_snd.comp
    (UpperRepairTrialLaw.data_measurable (m := m) (L := L) policy hm active origin q))
  exact measurableSet_le measurable_const (hmass.comp hsamples)

theorem badCycle_measurable (policy : Policy n) (hm : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (lam : ℝ) :
    MeasurableSet (badCycle (m := m) (L := L) policy hk chores active origin old q lam) :=
  measurableSet_eq_fun (RefinedUpperRepairTargets.approved_measurable chores active _ lam
    (prepared_measurable policy hm hk chores active origin old q)) measurable_const

theorem failed_measurable (policy : Policy n) (hm : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (eta lam : ℝ) :
    MeasurableSet (failed (m := m) (L := L) (r := r) policy hk chores active origin old q eta lam) :=
  measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp
    (RefinedUpperRepairOutputMeasurable.execute_measurable policy hm hk chores active
      (fun _ => origin) (fun _ => old) q eta lam id measurable_const (fun _ => measurable_const) measurable_id)))
    measurable_const

theorem failed_fiber (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (eta lam : ℝ) (x : Parameter k m L)
    (ha : x ∉ badCycle policy hk chores active origin old q lam) :
    {tape : Fin k → Fin r → UpperCircular.Circle | (x,tape) ∈ failed policy hk chores active origin old q eta lam} =
      {tape | (RefinedUpperBatchLoop.run policy
        (RefinedUpperCorrectionSetup.tasks active (prepared policy hk chores active origin old q x).2.1
          (UpperGridData.cuts (prepared policy hk chores active origin old q x).1)
          (RefinedUpperRepairTargets.targets chores active (prepared policy hk chores active origin old q x) eta lam) eta lam)
        (RefinedUpperCorrectionSetup.startState active (prepared policy hk chores active origin old q x).2.1
          (UpperGridData.cuts (prepared policy hk chores active origin old q x).1)
          (RefinedUpperRepairTargets.targets chores active (prepared policy hk chores active origin old q x) eta lam) eta)
        tape).2.stopped = true} := by
  have hap : RefinedUpperRepairTargets.approved chores active (prepared policy hk chores active origin old q x) lam = true :=
    Bool.eq_true_of_not_eq_false ha
  dsimp only [prepared] at hap
  ext tape
  simp only [failed,mem_ofPred_eq,RefinedUpperRepairLaw.execute,RefinedUpperRepairProgram.execute,
    RefinedUpperRepairProgram.finish_stopped,RefinedUpperRepairTrial.execute,RefinedUpperRepairTrial.after,
    prepared,hap,ite_true]

end EnvyFreeResearch.Full.RefinedUpperRepairEvents
