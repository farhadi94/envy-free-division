import EnvyFreeResearch.Full.UpperGlobalRunChancePrefix

/-! Unconditional attempt-versus-success inequalities for the concrete
reachable Shrink and Repair phases on the original infinite random stream. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperGlobalTape UpperStageMeasurable
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (whole : Set ℝ) (chores : Bool) (initial : Phase n) (hinit : initial.Valid μ chores whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hmeas : MeasurablePolicy policy) (fallback : Fin n)
  (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
  (haccept : Measurable (Function.uncurry (Phase.accepted policy chores)))
include hinit hpolicy hmeas hstep haccept

theorem shrink_original_attempt_bound (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .shrink t) ≤
      (64/63 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .shrink t) := by
  apply finitePrefix_attempt_bound policy fallback chores hstep haccept initial .shrink t _ (by finiteness)
  intro pastDraws hp
  exact valid_shrink_phase_factor μ whole chores _
    (finiteRun_valid μ whole chores initial hinit policy hpolicy fallback t pastDraws) hp policy hpolicy hmeas

theorem repair_original_attempt_bound (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .repair t) ≤
      (64/63 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .repair t) := by
  apply finitePrefix_attempt_bound policy fallback chores hstep haccept initial .repair t _ (by finiteness)
  intro pastDraws hp
  exact valid_repair_phase_factor μ whole chores _
    (finiteRun_valid μ whole chores initial hinit policy hpolicy fallback t pastDraws) hp policy hpolicy hmeas

end EnvyFreeResearch.Full.UpperGlobalPhysical
