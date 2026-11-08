import EnvyFreeResearch.Full.UpperRepairSnapshot

/-! Concrete original-population inputs for the Snapshot contrast theorem.
Preparation retains the full owner/target tape and independent labels. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairJobs UpperRepairPreparationChecks UpperRepairTrialProgram
  UpperRepairAllocation UpperSnapshotContrast UpperRepairParameters

abbrev Preparation (n k : ℕ) := (Fin (UpperRepair.fine n) → Fin k × I) × Labels k (UpperRepair.coarse n)

def preparationLaw (n k : ℕ) : Measure (Preparation n k) :=
  (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (UpperRepair.fine n)).prod UpperReserve.labelLaw

instance preparationLaw_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (preparationLaw n k) := by
  unfold preparationLaw
  infer_instance

variable {n k : ℕ} [Nonempty (Fin k)]

def prepData (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) x.1

def prepReserve (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  UpperGridData.reserve (prepData policy active origin x) (UpperRepair.reserveMark n) x.2

def prepWeights (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  dataWeights active origin (prepData policy active origin x) (UpperRepair.repeats n) (UpperRepair.reserveMark n) x.2

def prepOld (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (x : Preparation n k) := oldMatrix active old (prepReserve policy active origin x)

def view (p : UpperRepair.Tape n k) : Preparation n k × IsolationDraw k (UpperRepair.repeats n) :=
  ((p.2.1.1, p.1), p.2.1.2)

def actualMatrix (policy : Policy n) (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (p : UpperRepair.Tape n k) :=
  dataMatrix hk active origin old (prepData policy active origin (view p).1) (UpperRepair.repeats n)
    (UpperRepair.reserveMark n) p.1 p.2.1.2.1 p.2.1.2.2

def actualTargets (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : UpperRepair.Tape n k) :=
  dataTargets hk (UpperRepair.coarse n) chores active origin old (prepData policy active origin (view p).1)
    (UpperRepair.repeats n) (UpperRepair.reserveMark n) p.1 p.2.1.2.1 p.2.1.2.2 (UpperRepair.gapMultiplier n)

def actualStage (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : UpperRepair.Tape n k) :=
  UpperCorrectionStageProgram.executeStage policy active (prepReserve policy active origin (view p).1)
    (UpperGridData.cuts (prepData policy active origin (view p).1))
    (actualTargets policy hk chores active origin old p) (UpperRepair.cellBound n) (UpperRepair.gapMultiplier n) p.2.2

def actualError (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : UpperRepair.Tape n k) :=
  recordedError active (prepReserve policy active origin (view p).1)
    (actualTargets policy hk chores active origin old p) (actualStage policy hk chores active origin old p)

theorem view_preserves : MeasurePreserving (view (n := n) (k := k)) (UpperRepair.law n k)
    ((preparationLaw n k).prod (isolationLaw k (UpperRepair.repeats n))) :=
  UpperProductViews.isolation_view UpperReserve.labelLaw
    (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (UpperRepair.fine n))
    (isolationLaw k (UpperRepair.repeats n)) (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))

theorem prepWeights_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (j : Job k) (a : Fin (UpperRepair.repeats n)) (i : Fin k) :
    Measurable (fun x => prepWeights policy active origin x j a i) := by
  have hd : Measurable (prepData policy active origin) :=
    UpperLogicalPreparationGuard.fixed_origin_projection_measurable
      (fun z : State n × (Fin (UpperRepair.fine n) → Fin k × I) =>
        UpperGridMerge.prepare policy active z.1 (UpperRepair.coarse n) (UpperRepair.fine n) z.2)
      (UpperGridMerge.prepare_measurable policy hmeas active (UpperRepair.coarse n) (UpperRepair.fine n)) origin
  exact dataWeights_measurable active (fun _ => origin) (prepData policy active origin) (UpperRepair.repeats n)
    (UpperRepair.reserveMark n) Prod.snd measurable_const hd (fun c => (measurable_pi_apply c).comp measurable_snd) j a i

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (hnear : Near chores μ active origin old (UpperRepair.nearError n))
  (p : UpperRepair.Tape n k) (hsuccess : (UpperRepair.execute policy hk chores active origin old p).2.2 = false)

set_option hygiene false
local notation "Z" => normalizedValues (fun i => μ (active i)) (domain (prepReserve policy active origin (view p).1).cells)
  (fun j => domain ((UpperRepair.execute policy hk chores active origin old p).1 j).cells)
local notation "V" => actualMatrix policy hk active origin old p
local notation "t" => actualTargets policy hk chores active origin old p
local notation "e" => actualError policy hk chores active origin old p

include hpolicy hinj hgood hpositive hold holdbuffer hnear hsuccess in
theorem original_joining :
    (∀ i j, Z i j = paid V (assignment chores V) t i j + e i j) ∧
      (∀ i j, |e i j| ≤ signedGap chores Z i j) ∧ (∀ i, e i i = 0) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hf := original_population_facts n k hk hkn
  have hs := scale_large n
  have hell : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  exact successful_joining μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer
    (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.repeats n) hf.representative_budget
    (UpperRepair.reserveMark n) (reserve_positive hs hell) (UpperRepair.cutoff n) (UpperRepair.cellBound n)
    (UpperRepair.gapMultiplier n) (UpperRepair.nearError n) (fineCap_positive hs hell).le (multiplier_positive hs).le
    (by have := hf.rounding_margin; change (k : ℝ)^2 ≤ multiplier (scale n); linarith [multiplier_positive hs])
    hf.correction_extra (oldError_positive hs hell).le hnear hf.normalized_cell_cap hf.total_target_budget p hsuccess

include hpolicy hgood hpositive hsuccess in
theorem original_reserve (i : Fin k) :
    (UpperRepair.reserveMark n : ℝ) / 2 * (μ (active i)).real (domain origin.cells) ≤
      (μ (active i)).real (domain (prepReserve policy active origin (view p).1).cells) ∧
    (μ (active i)).real (domain (prepReserve policy active origin (view p).1).cells) ≤
      3 * (UpperRepair.reserveMark n : ℝ) / 2 * (μ (active i)).real (domain origin.cells) :=
  successful_reserve μ policy hpolicy hk chores active origin hgood hpositive old (UpperRepair.coarse n) (UpperRepair.fine n)
    (UpperRepair.repeats n) (UpperRepair.reserveMark n) (UpperRepair.cutoff n) (UpperRepair.cellBound n)
    (UpperRepair.gapMultiplier n) p hsuccess i

end EnvyFreeResearch.Full.UpperRepairSnapshot
