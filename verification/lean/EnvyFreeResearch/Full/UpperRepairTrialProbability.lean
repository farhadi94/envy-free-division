import EnvyFreeResearch.Full.UpperRepairTrialRejection
import EnvyFreeResearch.Full.UpperRepairCorrectionProbability

/-! Unconditional failure bound for the actual ordinary-query Repair trial.
All three events live on one complete original tape; rejected grid and
correction attempts are the same attempts counted by program_cost. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepairTrialProbability

open UpperRecordedDomain UpperCircularStage UpperCorrectionExecution UpperStageMeasurable
  UpperRepairTrialProgram UpperRepairTrialLaw UpperRepairTrialRejection UpperLogicalIsolation
  UpperLogicalPreparationGuard UpperRepairPreparationProbability UpperRepairPreparationChecks
  UpperRepairCorrectionProbability UpperRepairJobs

variable {n k q m L : ℕ} [Nonempty (Fin k)]

theorem failed_subset (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ) :
    Failed policy hk chores active origin old q m L theta cap eta lam ⊆
      (BadPreparation policy active origin q m L theta cap ∪
        BadCycle policy hk chores active origin old q m L theta cap lam) ∪
      {p | correctionRejected policy hk chores active origin old q m L theta cap eta lam p = true} := by
  intro p hp
  rcases (failed_iff policy hk chores active origin old q m L theta cap eta lam p).mp hp with ha | hc
  · rw [approved_actual] at ha
    by_cases hg : guard policy active origin q m (requests k L) theta cap p.2.1.1 p.1 = true
    · have hcycle := (Bool.and_eq_false_iff.mp ha).resolve_left (by rw [hg]; decide)
      exact Or.inl (Or.inr ⟨hg, Bool.eq_true_of_not_eq_false' hcycle⟩)
    · exact Or.inl (Or.inl (Bool.eq_false_iff.mpr hg))
  · exact Or.inr hc

theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j)) (q m L : ℕ)
    (hrepresentatives : 2 * (jobCount k * L) < q + 1)
    (hgrid : UpperRecordedQuantiles.count (Agent := Fin k) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam b tau : ℝ)
    (hcap : 0 < cap) (heta : 0 ≤ eta) (hlam : 0 < lam) (hb : 0 < b) (htau : 0 ≤ tau)
    (hnear : Near chores μ active origin old tau)
    (hcell : cellCap q theta ≤ eta) (hbudget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * cap ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16) :
    trialLaw k q m L (Failed policy hk chores active origin old q m L theta cap eta lam) ≤
      ENNReal.ofReal (failureBudget (Agent := Fin k) q m (jobCount k * L) theta cap) +
      ENNReal.ofReal (isolationBound k L lam) +
      ENNReal.ofReal (8 * k * eta * cap / lam +
        16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ))) := by
  have hg := preparation_probability μ policy hpolicy hmeas active origin hgood hpositive
    q m L hrepresentatives hgrid theta htheta cap hcap
  have hc := cycle_probability μ policy hpolicy hmeas hk chores active origin hgood hpositive old
    q m L hrepresentatives theta cap lam hlam.le
  have hp := UpperRepairCorrectionProbability.probability_le μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold q m L theta htheta cap eta lam b tau heta hlam hcap.le hb htau
    hnear hcell hbudget hsize hquarter hmargin
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hfirst : 0 ≤ 8 * ((k : ℝ) * eta) * cap / lam := by positivity
  have hsecond : 0 ≤ 16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ)) := by
    positivity
  calc
    _ ≤ trialLaw k q m L ((BadPreparation policy active origin q m L theta cap ∪
        BadCycle policy hk chores active origin old q m L theta cap lam) ∪
        {p | correctionRejected policy hk chores active origin old q m L theta cap eta lam p = true}) :=
      measure_mono (failed_subset policy hk chores active origin old q m L theta cap eta lam)
    _ ≤ (trialLaw k q m L (BadPreparation policy active origin q m L theta cap) +
        trialLaw k q m L (BadCycle policy hk chores active origin old q m L theta cap lam)) +
        trialLaw k q m L {p | correctionRejected policy hk chores active origin old q m L theta cap eta lam p = true} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (failureBudget (Agent := Fin k) q m (jobCount k * L) theta cap) +
        ENNReal.ofReal (isolationBound k L lam)) +
        (ENNReal.ofReal (8 * ((k : ℝ) * eta) * cap / lam) +
          ENNReal.ofReal (16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / ((theta : ℝ) * b * (m + 1 : ℕ)))) :=
      add_le_add (add_le_add hg hc) hp
    _ = _ := by rw [← ENNReal.ofReal_add hfirst hsecond]; congr 2; ring

end EnvyFreeResearch.Full.UpperRepairTrialProbability
