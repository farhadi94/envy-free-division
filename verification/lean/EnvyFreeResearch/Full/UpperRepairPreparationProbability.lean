import EnvyFreeResearch.Full.UpperRepairTrialLaw
import EnvyFreeResearch.Full.UpperProductViews

/-! Preparation and actual seed-cycle rejection on the same complete
original product law used by the physical correction trial. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairPreparationProbability

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairTrialProgram UpperRepairTrialLaw
  UpperLogicalPreparationGuard UpperRepairJobs

variable {n k q m L : ℕ} [Nonempty (Fin k)]

def BadPreparation (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (theta : I) (cap : ℝ) : Set (Tape k q m L) :=
  {p | guard policy active origin q m (requests k L) theta cap p.2.1.1 p.1 = false}

def BadCycle (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap lam : ℝ) : Set (Tape k q m L) :=
  {p | guard policy active origin q m (requests k L) theta cap p.2.1.1 p.1 = true ∧
    cycleReject chores (cachedMatrix hk policy active origin old q m L p.2.1.1 theta p.1 p.2.1.2.1 p.2.1.2.2)
      (disagreement policy active origin q m p.2.1.1 theta p.1) lam = true}

theorem preparation_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q m L : ℕ) (hbudget : 2 * (jobCount k * L) < q + 1)
    (hgrid : UpperRecordedQuantiles.count (Agent := Fin k) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    trialLaw k q m L (BadPreparation policy active origin q m L theta cap) ≤
      ENNReal.ofReal (failureBudget (Agent := Fin k) q m (jobCount k * L) theta cap) := by
  have hv := UpperProductViews.preparation_view
    (UpperReserve.labelLaw : Measure (Labels k q))
    (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m)
    (isolationLaw k L) (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))
  have hbad := measurableSet_eq_fun
    (guard_measurable policy hmeas active origin q m (requests k L) theta cap) (measurable_const (a := false))
  have heq := hv.measure_preimage hbad.nullMeasurableSet
  change trialLaw k q m L (BadPreparation policy active origin q m L theta cap) =
    originalLaw (Agent := Fin k) q m {p | guard policy active origin q m (requests k L) theta cap p.1 p.2 = false} at heq
  rw [heq]
  simpa only [requests_length] using original_tape_failure_probability μ policy hpolicy hmeas active origin hgood hpositive
    q m (requests k L) (by simpa only [requests_length] using hbudget) hgrid theta htheta cap hcap

theorem cycle_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (old : Fin k → State n)
    (q m L : ℕ) (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (cap lam : ℝ) (hlam : 0 ≤ lam) :
    trialLaw k q m L (BadCycle policy hk chores active origin old q m L theta cap lam) ≤
      ENNReal.ofReal (isolationBound k L lam) := by
  let Prep := (Fin m → Fin k × I) × Labels k q
  let View := Prep × IsolationDraw k L
  have hv := UpperProductViews.isolation_view
    (UpperReserve.labelLaw : Measure (Labels k q))
    (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m)
    (isolationLaw k L) (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))
  have hd0 : Measurable (fun p : Prep => UpperGridMerge.prepare policy active origin q m p.1) :=
    fixed_origin_projection_measurable
      (fun p : State n × (Fin m → Fin k × I) => UpperGridMerge.prepare policy active p.1 q m p.2)
      (UpperGridMerge.prepare_measurable policy hmeas active q m) origin
  have hd := hd0.comp (measurable_fst : Measurable (Prod.fst : View → Prep))
  have hl (c) : Measurable (fun p : View => p.1.2 c) :=
    (measurable_pi_apply c).comp (measurable_snd.comp measurable_fst)
  have hV (i j) : Measurable (fun p : View =>
      cachedMatrix hk policy active origin old q m L p.1.1 theta p.1.2 p.2.1 p.2.2 i j) := by
    simpa only [dataMatrix_execute] using dataMatrix_measurable hk active (fun _ : View => origin)
      (fun _ : View => old) (fun p : View => UpperGridMerge.prepare policy active origin q m p.1.1)
      L theta (fun p => p.1.2) (fun p => p.2.1) (fun p => p.2.2)
      measurable_const (fun _ => measurable_const) hd hl (measurable_fst.comp measurable_snd)
      (fun a => (measurable_pi_apply a).comp (measurable_snd.comp measurable_snd)) i j
  have hA (i j) : Measurable (fun p : View => disagreement policy active origin q m p.1.1 theta p.1.2 i j) := by
    simpa only [dataDisagreement_execute] using dataDisagreement_measurable active
      (fun p : View => UpperGridMerge.prepare policy active origin q m p.1.1) theta
      (fun p => p.1.2) hd hl i j
  have hg := (guard_measurable policy hmeas active origin q m (requests k L) theta cap).comp
    (measurable_fst : Measurable (Prod.fst : View → Prep))
  have hc := cycleReject_measurable chores _ _ lam hV hA
  have hbad := (measurableSet_eq_fun hg (measurable_const (a := true))).inter
    (measurableSet_eq_fun hc (measurable_const (a := true)))
  have heq := hv.measure_preimage hbad.nullMeasurableSet
  change trialLaw k q m L (BadCycle policy hk chores active origin old q m L theta cap lam) =
    ((originalLaw (Agent := Fin k) q m).prod (isolationLaw k L))
      {p | guard policy active origin q m (requests k L) theta cap p.1.1 p.1.2 = true ∧
        cycleReject chores (cachedMatrix hk policy active origin old q m L p.1.1 theta p.1.2 p.2.1 p.2.2)
          (disagreement policy active origin q m p.1.1 theta p.1.2) lam = true} at heq
  rw [heq]
  simpa only [cachedMatrix, seedSystem, coreMatrix] using original_cycle_probability μ policy hpolicy hmeas
    active origin hgood hpositive hk q m L hbudget theta cap old lam hlam chores (originalLaw q m)

end EnvyFreeResearch.Full.UpperRepairPreparationProbability
