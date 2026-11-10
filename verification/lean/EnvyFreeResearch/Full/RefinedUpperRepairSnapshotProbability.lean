import EnvyFreeResearch.Full.RefinedUpperRepairSnapshotConfigured

/-! Unconditional contrast preservation for the actual physical ordinary
Repair trial. Joining, correction errors, the two-sided reserve guard and
failure probability are proved implementation facts; only the Snapshot
candidate's pre-seed baseline contrast is an input to this adapter. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.RefinedUpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairPreparationChecks RefinedUpperRepairAllocation UpperSnapshotContrast

variable {n k : ℕ} [Nonempty (Fin k)]

def Success (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) : Set (RefinedUpperRepair.Tape n k) :=
  {p | (RefinedUpperRepair.execute policy hk chores active origin old p).2.2 = false}

def MarginEvent (μ : Fin n → Measure ℝ) (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n) (Lambda : ℝ) : Set (RefinedUpperRepair.Tape n k) :=
  {p | p ∈ Success policy hk chores active origin old ∧ ∃ a b, a ≠ b ∧
    0 < physicalGap chores (fun i => μ (active i))
      (fun j => domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 j).cells) a b ∧
    Lambda / 8 * (μ (active a)).real (domain (RefinedUpperRepair.execute policy hk chores active origin old p).2.1.cells) ≤
      physicalGap chores (fun i => μ (active i))
        (fun j => domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 j).cells) a b}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))

include hpolicy hmeas hinj hgood hpositive hold hnear in
theorem original_trial_margin_of_failure_bound
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history)
    (chosen : Preparation n k → Selection k) (hchosen : Measurable chosen)
    (hfailure : (RefinedUpperRepair.law n k).real (Success policy hk chores active origin old)ᶜ < 1/64)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ Success policy hk chores active origin old,
      Lambda ≤
        contrast (prepOld policy active origin old (view p).1)
          (chosen (view p).1).1.1 (chosen (view p).1).1.2
          (chosen (view p).1).2.1 (chosen (view p).1).2.2) :
    31 / 64 < (RefinedUpperRepair.law n k).real (MarginEvent μ policy hk chores active origin old Lambda) := by
  have hj (p : RefinedUpperRepair.Tape n k) (hp : p ∈ Success policy hk chores active origin old) :=
    original_joining μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer hnear p hp
  have hr (p : RefinedUpperRepair.Tape n k) :=
    original_reserve μ policy hpolicy active hinj origin hgood hpositive p
  exact original_trial_physical_margin hk chores (preparationLaw n k) (RefinedUpperRepair.law n k) view view_preserves
    (prepWeights policy active origin) (prepOld policy active origin old) chosen
    (prepWeights_measurable policy hmeas active origin) hchosen (fun i => μ (active i)) (domain origin.cells)
    (fun p => domain (prepReserve policy active origin (view p).1).cells)
    (fun p => domain (RefinedUpperRepair.execute policy hk chores active origin old p).2.1.cells)
    (fun p j => domain ((RefinedUpperRepair.execute policy hk chores active origin old p).1 j).cells)
    (fun p => assignment chores (actualMatrix policy hk active origin old p))
    (actualTargets policy hk chores active origin old) (actualError policy hk chores active origin old)
    (Success policy hk chores active origin old)
    hfailure
    (fun p hp => (hj p hp).1) (fun p hp => (hj p hp).2.1) Lambda 1 hLambda (by norm_num)
    (by simpa only [div_one] using hbaseline) hpositive (fun p _ i => hr p i)
    (fun p hp => (RefinedUpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
      holdpair holdbuffer holdHistory p hp).residue_subset)

end EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
