import EnvyFreeResearch.Full.UpperSnapshotSmallFirstLaws
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateCircle

/-! The actual small-candidate branching test supplies both circular groups.
No lower mass assumption on the chosen subdomain is postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperLogicalPreparation UpperDomainDifference Chores
variable {n m : ℕ}

/-- If t≤1/2, either branch leaves at least t of the original cutter mass
available to the first circular draw. -/
theorem first_source_fraction
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1)))
    (t : ℝ) (ht : t ≤ 1 / 2) :
    t * (μ cutter).real (domain origin.cells) ≤
      (μ cutter).real (domain (firstSource origin cutter cuts selected t).cells) := by
  rw [← total_correct μ _ (firstSource_wellFormed μ origin hgood cutter cuts selected t),
    firstSource_total μ origin hgood cutter cuts selected t, ← total_correct μ origin hgood cutter]
  have hM : 0 ≤ total origin cutter := by rw [total_correct μ origin hgood]; positivity
  by_cases hfill : total (UpperLogicalPreparation.retain origin cuts selected) cutter < t * total origin cutter
  · simp only [firstFill, hfill, decide_true, ite_true]
    nlinarith
  · simp only [firstFill, hfill, decide_false, Bool.false_eq_true, ite_false]
    exact le_of_not_gt hfill

theorem first_source_subset (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) :
    domain (firstSource origin cutter cuts selected t).cells ⊆ domain origin.cells := by
  unfold firstSource
  split_ifs
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    exact mem_domain.mpr ⟨c, (List.mem_filter.mp hc).1, hxc⟩
  · exact retain_subset origin cuts selected

/-- The second group's supply is determined by the actual first cut's exact
mass equation, for every first shared start and every prior query history. -/
theorem second_source_fraction
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells))
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (start : UpperSnapshotSmall.Circle) :
    t * (μ cutter).real (domain origin.cells) ≤
      (μ cutter).real (domain (firstRemainder policy origin cutter cuts selected t start).cells) := by
  rw [firstRemainder_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
    selected t ht (by linarith) start]
  exact mul_le_mul_of_nonneg_right (by linarith) hpositive.le

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
