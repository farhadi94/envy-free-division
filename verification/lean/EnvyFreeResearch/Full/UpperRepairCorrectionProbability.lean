import EnvyFreeResearch.Full.UpperRepairTrialLaw

/-! The correction rejection estimate instantiated with the actual original
sampler, actual cache guard, seed matrix and ideal targets, including the
independent isolation coordinates in the retained preparation parameter. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairCorrectionProbability

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairPreparationChecks
  UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram UpperCorrectionRejectionMeasurable

variable {n k q m L : ℕ} [Nonempty (Fin k)]

def reserve (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (q : ℕ) (theta : I)
    (labels : Labels k q) (x : Parameter k m L) : State n :=
  UpperGridData.reserve (data policy active origin q x) theta labels

def cuts (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (q : ℕ)
    (_labels : Labels k q) (x : Parameter k m L) : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 2) → ℝ :=
  UpperGridData.cuts (data policy active origin q x)

def targets (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q L : ℕ) (theta : I) (lam : ℝ)
    (labels : Labels k q) (x : Parameter k m L) : Fin k → ℝ :=
  dataTargets hk q chores active origin old (data policy active origin q x) L theta labels x.2.1 x.2.2 lam

def ready (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q L : ℕ) (theta : I) (cap lam : ℝ)
    (labels : Labels k q) (x : Parameter k m L) : Bool :=
  approved hk chores active origin old (data policy active origin q x) L theta cap lam labels x.2.1 x.2.2

def correctionRejected (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) : Bool :=
  rejected policy active (reserve policy active origin q theta p.1 p.2.1)
    (cuts policy active origin q p.1 p.2.1)
    (targets policy hk chores active origin old q L theta lam p.1 p.2.1) eta lam
    (ready policy hk chores active origin old q L theta cap lam p.1 p.2.1) p.2.2

set_option maxHeartbeats 1000000 in
theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j)) (q m L : ℕ)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam b tau : ℝ)
    (heta : 0 ≤ eta) (hlam : 0 < lam) (hcap : 0 ≤ cap) (hb : 0 < b) (htau : 0 ≤ tau)
    (hnear : Near chores μ active origin old tau)
    (hcell : cellCap q theta ≤ eta) (hbudget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * cap ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16) :
    trialLaw k q m L {p | correctionRejected policy hk chores active origin old q m L theta cap eta lam p = true} ≤
      ENNReal.ofReal (8 * ((k : ℝ) * eta) * cap / lam) +
        ENNReal.ofReal (16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ))) := by
  let sampleLaw := UpperMixtureSampling.mixture μ active origin.cells
  let : IsProbabilityMeasure sampleLaw := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  let Y := Labels k q × Parameter k m L
  have hd : Measurable (fun z : Y => data policy active origin q z.2) :=
    (data_measurable policy hmeas active origin q).comp measurable_snd
  have hl (p) : Measurable (fun z : Y => z.1 p) := (measurable_pi_apply p).comp measurable_fst
  have hp : Measurable (fun z : Y => z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hh (j) : Measurable (fun z : Y => z.2.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hr : Measurable (Function.uncurry (reserve (m := m) (L := L) policy active origin q theta)) :=
    UpperGridData.reserve_measurable _ theta _ hd hl
  have hcuts (e) : Measurable (fun z : Y => cuts policy active origin q z.1 z.2 e) :=
    (measurable_pi_apply e).comp (UpperGridData.cuts_measurable _ hd)
  have ht (j) : Measurable (fun z : Y => targets policy hk chores active origin old q L theta lam z.1 z.2 j) :=
    dataTargets_measurable hk q chores active (fun _ : Y => origin) (fun _ : Y => old)
      (fun z : Y => data policy active origin q z.2) L theta (fun z : Y => z.1)
      (fun z : Y => z.2.2.1) (fun z : Y => z.2.2.2) lam
      measurable_const (fun _ => measurable_const) hd hl hp hh j
  have ha : Measurable (Function.uncurry (ready (m := m) policy hk chores active origin old q L theta cap lam)) :=
    approved_measurable hk chores active (fun _ : Y => origin) (fun _ : Y => old)
      (fun z : Y => data policy active origin q z.2) L theta cap lam (fun z : Y => z.1)
      (fun z : Y => z.2.2.1) (fun z : Y => z.2.2.2)
      measurable_const (fun _ => measurable_const) hd hl hp hh
  apply UpperOriginalCorrectionProbability.probability_le μ policy hpolicy hmeas active hinj origin.cells
    (fun labels => (frozenReserveState policy active origin q theta labels).cells) hpositive
    (UpperRecordedQuantiles.run policy active origin q).1
    (fun i => (UpperGridMerge.coarse_endpoints μ policy hpolicy active origin hgood hpositive q i).1)
    sampleLaw (UpperMixtureSampling.mixture_supported μ active origin.cells) rfl
    UpperReserve.labelLaw (parameterLaw k m L)
    (fun x => (data policy active origin q x).2.1)
    (original_samples_law μ policy hpolicy hmeas active origin hgood hpositive q)
    (reserve policy active origin q theta) hr
    (fun labels x => final_reserve_eq_frozen μ policy hpolicy active origin hgood hpositive q m x.1 theta labels)
    (cuts policy active origin q) hcuts (fun _ x => data_cuts policy active origin q x)
    (targets policy hk chores active origin old q L theta lam) ht
    (ready policy hk chores active origin old q L theta cap lam) ha
    eta lam cap (theta : ℝ) b heta hlam hcap htheta hb hsize hquarter hmargin
    (fun labels x => reserveCells (UpperGridData.parent (data policy active origin q x)) theta labels)
  · intro labels x hready
    exact approved_checks μ policy hpolicy active origin hgood hpositive hk chores old hold q m L x.1
      theta htheta cap eta lam tau labels x.2.1 x.2.2 htau hnear hlam.le hcell hbudget hready
  · intro labels x _
    exact reserveState_subset μ policy hpolicy active origin hgood hpositive q m x.1 theta labels
  · intro labels x hready i
    have hpass := ((approved_iff hk chores active origin old _ L theta cap lam labels x.2.1 x.2.2).mp hready).1
    rw [data, UpperGridData.guard_execute] at hpass
    exact UpperLogicalPreparationGuard.passing_lower_mass μ policy hpolicy active origin hgood hpositive
      q m (requests k L) theta cap x.1 labels hpass i

end EnvyFreeResearch.Full.UpperRepairCorrectionProbability
