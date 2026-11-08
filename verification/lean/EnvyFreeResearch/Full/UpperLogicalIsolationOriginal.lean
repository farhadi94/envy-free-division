import EnvyFreeResearch.Full.UpperLogicalIsolationProbability

/-! The actual original fine/label tape times fresh seed randomness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRepairJobs Chores
variable {n k : ℕ} [Nonempty (Fin k)]

/-- The seed rejection bound holds over any original law of the full fine
and label tape, with the actual preparation guard and actual cache selectors.
In particular it applies directly to `UpperLogicalPreparationGuard.originalLaw`. -/
theorem original_cycle_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (hk : 2 ≤ k) (q m L : ℕ) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (cap : ℝ) (old : Fin k → State n) (lam : ℝ) (hlam : 0 ≤ lam) (chores : Bool)
    (P : Measure ((Fin m → Fin k × I) × (Parent k q → I))) [IsProbabilityMeasure P] :
    (P.prod (isolationLaw k L)) {p |
      guard policy active origin q m (requests k L) theta cap p.1.1 p.1.2 = true ∧
      cycleReject chores
        (coreMatrix hk (weights policy active origin q m L p.1.1 theta p.1.2)
          (oldMatrix active old (reserveState policy active origin q m p.1.1 theta p.1.2)) p.2.1 p.2.2)
        (disagreement policy active origin q m p.1.1 theta p.1.2) lam = true} ≤
        ENNReal.ofReal (isolationBound k L lam) := by
  let X := (Fin m → Fin k × I) × (Parent k q → I)
  have hd : Measurable (fun p : X => UpperGridMerge.prepare policy active origin q m p.1) :=
    fixed_origin_projection_measurable
      (fun p : State n × (Fin m → Fin k × I) => UpperGridMerge.prepare policy active p.1 q m p.2)
      (UpperGridMerge.prepare_measurable policy hmeas active q m) origin
  have hl (c : Parent k q) : Measurable (fun p : X => p.2 c) := (measurable_pi_apply c).comp measurable_snd
  have hw (j : Job k) (a : Fin L) (i : Fin k) :
      Measurable (fun p : X => weights policy active origin q m L p.1 theta p.2 j a i) := by
    simpa only [dataWeights_execute] using dataWeights_measurable active (fun _ : X => origin)
      (fun p : X => UpperGridMerge.prepare policy active origin q m p.1) L theta Prod.snd
      measurable_const hd hl j a i
  have hr : Measurable (fun p : X => reserveState policy active origin q m p.1 theta p.2) := by
    simpa only [UpperGridData.reserve_execute] using UpperGridData.reserve_measurable
      (fun p : X => UpperGridMerge.prepare policy active origin q m p.1) theta Prod.snd hd hl
  have hA (i j : Fin k) : Measurable (fun p : X => disagreement policy active origin q m p.1 theta p.2 i j) := by
    simpa only [dataDisagreement_execute] using dataDisagreement_measurable active
      (fun p : X => UpperGridMerge.prepare policy active origin q m p.1) theta Prod.snd hd hl i j
  exact family_cycle_probability hk P
    (fun p : X => guard policy active origin q m (requests k L) theta cap p.1 p.2)
    (guard_measurable policy hmeas active origin q m (requests k L) theta cap)
    (fun p : X => weights policy active origin q m L p.1 theta p.2)
    (fun p : X => oldMatrix active old (reserveState policy active origin q m p.1 theta p.2))
    (fun p : X => disagreement policy active origin q m p.1 theta p.2) hw
    (oldMatrix_measurable active (fun _ : X => old) _ (fun _ => measurable_const) hr) hA
    (fun _ _ => UpperPayments.cellGap_nonneg _) (fun _ _ => UpperPayments.cellGap_symmetric _)
    lam hlam (fun p hp => weights_gap μ policy hpolicy active origin hgood hpositive q m L p.1 hbudget theta cap p.2 hp) chores

end EnvyFreeResearch.Full.UpperLogicalIsolation
