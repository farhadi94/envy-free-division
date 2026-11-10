import EnvyFreeResearch.Full.RefinedUpperPreparationFixed
import EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
import EnvyFreeResearch.Full.RefinedUpperRepair

/-! Concrete original-population inputs for the Snapshot contrast theorem.
Preparation retains the full owner/target tape and independent labels. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairJobs UpperRepairPreparationChecks UpperRepairTrialProgram
  RefinedUpperRepairAllocation UpperSnapshotContrast RefinedUpperPreparation RefinedUpperParameterCounts RefinedUpperRepairParameters
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale)

abbrev Preparation (n k : ℕ) := Fin (RefinedUpperRepair.fine n) → Fin k × I

def preparationLaw (n k : ℕ) : Measure (Preparation n k) :=
  UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) (RefinedUpperRepair.fine n)
instance preparationLaw_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (preparationLaw n k) := by
  unfold preparationLaw
  infer_instance
variable {n k : ℕ} [Nonempty (Fin k)]

def prepData (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) x

def prepReserve (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  dataRetained active origin (prepData policy active origin x) (RefinedUpperRepair.repeats n)

def prepWeights (policy : Policy n) (active : Fin k → Fin n) (origin : State n) (x : Preparation n k) :=
  RefinedUpperPreparation.dataWeights active origin (prepData policy active origin x) (RefinedUpperRepair.repeats n)

def prepOld (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (x : Preparation n k) := oldMatrix active old (prepReserve policy active origin x)

def view (p : RefinedUpperRepair.Tape n k) : Preparation n k × IsolationDraw k (RefinedUpperRepair.repeats n) := p.1

def actualMatrix (policy : Policy n) (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) :=
  dataMatrix hk active origin old (prepData policy active origin p.1.1) (RefinedUpperRepair.repeats n) p.1.2.1 p.1.2.2

def actualTargets (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) :=
  RefinedUpperRepairTargets.targets chores active
    (RefinedUpperPreparationProgram.finish hk chores active origin old (prepData policy active origin p.1.1)
      (RefinedUpperRepair.repeats n) p.1.2.1 p.1.2.2)
    (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n)

def actualStage (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) :=
  RefinedUpperRepairFinalCache.executeStage policy active (prepReserve policy active origin (view p).1)
    (UpperGridData.cuts (prepData policy active origin (view p).1))
    (actualTargets policy hk chores active origin old p) (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n) p.2

def actualError (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : RefinedUpperRepair.Tape n k) :=
  recordedError active (prepReserve policy active origin (view p).1)
    (actualTargets policy hk chores active origin old p) (actualStage policy hk chores active origin old p)

theorem view_preserves : MeasurePreserving (view (n := n) (k := k)) (RefinedUpperRepair.law n k)
    ((preparationLaw n k).prod (isolationLaw k (RefinedUpperRepair.repeats n))) := measurePreserving_fst

set_option maxHeartbeats 1500000 in
theorem prepWeights_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (j : Job k) (a : Fin (RefinedUpperRepair.repeats n)) (i : Fin k) :
    Measurable (fun x => prepWeights policy active origin x j a i) := by
  have hd : Measurable (prepData policy active origin) :=
    RefinedUpperPreparation.prepare_fixed_measurable policy hmeas active origin
      (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n)
  exact RefinedUpperPreparation.dataWeights_measurable active (fun _ => origin) (prepData policy active origin)
    (RefinedUpperRepair.repeats n) measurable_const hd j a i

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
  (p : RefinedUpperRepair.Tape n k) (hsuccess : (RefinedUpperRepair.execute policy hk chores active origin old p).2.2 = false)

set_option hygiene false
local notation "Z" => normalizedValues (fun i => μ (active i)) (domain (prepReserve policy active origin (view p).1).cells)
  (fun j => domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 j).cells)
local notation "V" => actualMatrix policy hk active origin old p
local notation "t" => actualTargets policy hk chores active origin old p
local notation "e" => actualError policy hk chores active origin old p

include hpolicy hinj hgood hpositive hold holdbuffer hnear hsuccess in
theorem original_joining :
    (∀ i j, Z i j = paid V (assignment chores V) t i j + e i j) ∧
      (∀ i j, |e i j| ≤ signedGap chores Z i j) ∧ (∀ i, e i i = 0) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have ha := active_scale n k hkn
  have hs256 : 256 ≤ scale n := by exact_mod_cast (show (256 : ℝ) ≤ scale n from (by norm_num : (256 : ℝ) ≤ 2^42).trans hs)
  have hk256 : 256*k ≤ scale n := by exact_mod_cast (show (256 : ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact successful_joining μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) (RefinedUpperRepair.repeats n) (parent_budget hs he ha)
    (2*(RefinedUpperRepair.fine n : ℝ)) (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n)
    (RefinedUpperRepair.nearError n) (by unfold RefinedUpperRepair.cellBound fineCap; positivity)
    (by unfold RefinedUpperRepair.gapMultiplier multiplier; positivity) (linear_margin hs ha)
    (correction_spending hs he ha) (by unfold RefinedUpperRepair.nearError oldError; positivity)
    hnear (cell_cap hs he) (target_total hs he ha)
    (by exact_mod_cast cell_count hs256 (logarithm_positive hs) hk256 (by omega))
    p.1.1 p.1.2.1 p.1.2.2 p.2 hsuccess

include hpolicy hinj hgood hpositive in
theorem original_reserve (i : Fin k) :
    (1/2 : ℝ)*(μ (active i)).real (domain origin.cells) ≤
      (μ (active i)).real (domain (prepReserve policy active origin (view p).1).cells) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  exact retained_half μ policy hpolicy active origin hgood hpositive
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) (RefinedUpperRepair.repeats n)
    (parent_budget hs he (active_scale n k hkn)) p.1.1 i

end EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
