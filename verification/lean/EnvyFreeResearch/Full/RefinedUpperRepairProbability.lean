import EnvyFreeResearch.Full.RefinedUpperRepairEventProbability
import EnvyFreeResearch.Full.RefinedUpperTrialUnion
import EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks

/-! Unconditional failure probability for the actual finite Repair program.
All deterministic correction checks are derived from the raw input, and the
original random-tape law is preserved throughout the exceptional-event split. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepairProbability
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperRepairLaw RefinedUpperRepairEvents RefinedUpperRepairPreparationChecks
  UpperRepairPreparationChecks UpperPreparedEnvelopeMean
variable {n k m L r : ℕ} [Nonempty (Fin k)]

theorem probability_le
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c)) (q : ℕ)
    (hparent : 4*(UpperRepairJobs.jobCount k*L) ≤ q+1)
    (tau eta lam N : ℝ) (htau : 0 ≤ tau) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hnear : Near chores μ active origin old tau)
    (hcell : 2/(q+1 : ℝ) ≤ eta)
    (hbudget : (k : ℝ)*RefinedUpperRepairPreparationChecks.targetBudget k q L tau eta lam < 1/16)
    (hcount : (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1 : ℝ) ≤ N)
    (hsize : 16*(k : ℝ) ≤ lam) (hmargin : (k : ℝ)*lam*eta < 1/16)
    (δ : ℝ) (hδ : 0 < δ) (a b B : ℝ≥0∞)
    (hbadbound : ENNReal.ofReal (32*(k : ℝ)/7)*ENNReal.ofReal δ ≤ a)
    (henvelope : ENNReal.ofReal (8*eta*N/lam) ≤ b) (hfixed : a+B*b ≤ B) :
    trialLaw k m L r (failed policy hk chores active origin old q eta lam) ≤
      ENNReal.ofReal ((((4*(UpperLogicalIsolation.requests k L).length+
        4*(RefinedUpperActualCorrectionBound.finalJobs k).length : ℕ) : ℝ)/(m+1 : ℕ))/δ) +
      ENNReal.ofReal (UpperLogicalIsolation.isolationBound k L lam) +
      (k : ℝ≥0∞)*(B+b^r) := by
  have hgrid := grid_probability (m := m) (L := L) μ policy hp hm active origin hgood hpositive q δ hδ
  have hcycle := cycle_probability (m := m) (L := L) μ policy hp hm hk chores active origin hgood hpositive
    old q (by omega) lam hlam.le
  apply RefinedUpperTrialUnion.two_exception_product_bound (UpperRepairTrialLaw.parameterLaw k m L)
    (retryLaw k r) (failed policy hk chores active origin old q eta lam)
    (failed_measurable policy hm hk chores active origin old q eta lam)
    (badGrid μ policy active origin q δ) (badCycle policy hk chores active origin old q lam)
    (badGrid_measurable μ policy hm active origin hpositive q δ)
    (badCycle_measurable policy hm hk chores active origin old q lam) _ _ _ hgrid hcycle
  intro x hg hc
  rw [failed_fiber policy hk chores active origin old q eta lam x hc]
  let data := UpperGridMerge.prepare policy active origin q m x.1
  let p := prepared policy hk chores active origin old q x
  have hchecks := actual_checks μ policy hp active origin hgood hpositive hk chores old hold
    q m L x.1 hparent tau eta lam N htau hnear hlam.le hcell hbudget hcount x.2.1 x.2.2
  let law := UpperMixtureSampling.mixture μ active origin.cells
  letI : IsProbabilityMeasure law := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  have hbad : law (RefinedUpperStability.physicalBad μ policy active origin q
      (UpperLogicalIsolation.requests k L) (RefinedUpperActualCorrectionBound.finalJobs k) data.1 data.2.1) ≤
      ENNReal.ofReal δ := by
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    exact (lt_of_not_ge hg).le
  have h := RefinedUpperActualCorrectionBound.correction_probability μ policy hp hm active hinj origin
    hgood hpositive q m L x.1 hparent (RefinedUpperRepairTargets.targets chores active p eta lam)
    eta lam N heta hlam hN hsize hmargin (RefinedUpperRepairSeedIndices.reserved active origin data L)
    hchecks (ENNReal.ofReal δ) hbad a b B hbadbound henvelope hfixed r
  exact h

end EnvyFreeResearch.Full.RefinedUpperRepairProbability
