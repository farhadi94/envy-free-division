import EnvyFreeResearch.Full.UpperRepairSnapshotConfigured

/-! Unconditional contrast preservation for the actual physical ordinary
Repair trial. Joining, correction errors, the two-sided reserve guard and
failure probability are proved implementation facts; only the Snapshot
candidate's pre-seed baseline contrast is an input to this adapter. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairPreparationChecks UpperRepairAllocation UpperSnapshotContrast

variable {n k : ℕ} [Nonempty (Fin k)]

def Success (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) : Set (UpperRepair.Tape n k) :=
  {p | (UpperRepair.execute policy hk chores active origin old p).2.2 = false}

def MarginEvent (μ : Fin n → Measure ℝ) (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n) (Lambda : ℝ) : Set (UpperRepair.Tape n k) :=
  {p | p ∈ Success policy hk chores active origin old ∧ ∃ a b, a ≠ b ∧
    0 < physicalGap chores (fun i => μ (active i))
      (fun j => domain ((UpperRepair.execute policy hk chores active origin old p).1 j).cells) a b ∧
    Lambda / 8 * (μ (active a)).real (domain (UpperRepair.execute policy hk chores active origin old p).2.1.cells) ≤
      physicalGap chores (fun i => μ (active i))
        (fun j => domain ((UpperRepair.execute policy hk chores active origin old p).1 j).cells) a b}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (UpperRepair.nearError n))

include hpolicy hmeas hinj hgood hpositive hold hnear in
theorem failure_real_lt :
    (UpperRepair.law n k).real (Success policy hk chores active origin old)ᶜ < 1 / 64 := by
  have h := UpperRepair.failure_lt μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear hmeas
  have heq : (Success policy hk chores active origin old)ᶜ =
      {p | (UpperRepair.execute policy hk chores active origin old p).2.2 = true} := by
    ext p
    cases hs : (UpperRepair.execute policy hk chores active origin old p).2.2 <;> simp [Success, hs]
  rw [heq, measureReal_def]
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by norm_num : (1 / 64 : ℝ≥0∞) ≠ ⊤)).mpr h
  norm_num at hr ⊢
  exact hr

include hpolicy hmeas hinj hgood hpositive hold hnear in
theorem original_trial_margin
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history)
    (chosen : Preparation n k → Selection k) (hchosen : Measurable chosen)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ Success policy hk chores active origin old,
      Lambda / (UpperRepair.reserveMark n : ℝ) ≤
        contrast (prepOld policy active origin old (view p).1)
          (chosen (view p).1).1.1 (chosen (view p).1).1.2
          (chosen (view p).1).2.1 (chosen (view p).1).2.2) :
    31 / 64 < (UpperRepair.law n k).real (MarginEvent μ policy hk chores active origin old Lambda) := by
  have hj (p : UpperRepair.Tape n k) (hp : p ∈ Success policy hk chores active origin old) :=
    original_joining μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer hnear p hp
  have hr (p : UpperRepair.Tape n k) (hp : p ∈ Success policy hk chores active origin old) :=
    original_reserve μ policy hpolicy hk chores active origin hgood hpositive old p hp
  have htheta : 0 < (UpperRepair.reserveMark n : ℝ) :=
    UpperRepairParameters.reserve_positive (UpperRepairParameters.scale_large n)
      (by exact_mod_cast UpperRepairParameters.logarithm_positive (UpperRepairParameters.scale_large n))
  exact original_trial_physical_margin hk chores (preparationLaw n k) (UpperRepair.law n k) view view_preserves
    (prepWeights policy active origin) (prepOld policy active origin old) chosen
    (prepWeights_measurable policy hmeas active origin) hchosen (fun i => μ (active i)) (domain origin.cells)
    (fun p => domain (prepReserve policy active origin (view p).1).cells)
    (fun p => domain (UpperRepair.execute policy hk chores active origin old p).2.1.cells)
    (fun p j => domain ((UpperRepair.execute policy hk chores active origin old p).1 j).cells)
    (fun p => assignment chores (actualMatrix policy hk active origin old p))
    (actualTargets policy hk chores active origin old) (actualError policy hk chores active origin old)
    (Success policy hk chores active origin old)
    (failure_real_lt μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold hnear)
    (fun p hp => (hj p hp).1) (fun p hp => (hj p hp).2.1) Lambda (UpperRepair.reserveMark n) hLambda htheta
    hbaseline hpositive (fun p hp i => (hr p hp i).1)
    (fun p hp => (UpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
      holdpair holdbuffer holdHistory p hp).residue_subset)

end EnvyFreeResearch.Full.UpperRepairSnapshot
