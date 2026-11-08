import EnvyFreeResearch.Full.UpperSnapshotSmallFirstExecution

/-! Raw-unit supply and exact requested mass for the first candidate cut.
The source positivity is derived from the cached first-stage branch test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ}

def firstCircular (policy : Policy n) (origin : State n) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) : Set ℝ :=
  actualPrefix (by decide : 0 < 2) policy (firstSource origin cutter cuts selected t) cutter
    (singleTargets (firstAmount origin cutter cuts selected t)) start 1

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem retain_subset (origin : State n) (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) :
    domain (retain origin cuts selected).cells ⊆ domain origin.cells := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
  exact mem_domain.mpr ⟨c, (List.mem_filter.mp hc).1, hxc⟩

theorem first_source_supply (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells)) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < total (firstSource origin cutter cuts selected t) cutter ∧
    0 < firstDeficit origin cutter cuts selected t ∧
    firstDeficit origin cutter cuts selected t ≤ total (firstSource origin cutter cuts selected t) cutter := by
  have hp := retain_wellFormed μ origin hgood cuts selected
  have hM : 0 < total origin cutter := by rw [total_correct μ origin hgood]; exact hpositive
  have hpos : 0 ≤ total (retain origin cuts selected) cutter := by rw [total_correct μ _ hp]; positivity
  have hcomp : total (selectState origin (fun c => !positiveFlag cuts selected c)) cutter =
      total origin cutter - total (retain origin cuts selected) cutter := by
    rw [total_correct μ _ (selectState_wellFormed μ origin hgood _),
      total_correct μ origin hgood, total_correct μ _ hp]
    change (μ cutter).real (domain (origin.cells.filter (fun c => !positiveFlag cuts selected c))) = _
    rw [whole_filter_domain _ hgood.2.1]
    exact measureReal_sdiff (retain_subset origin cuts selected) (domain_measurable _)
  by_cases hf : total (retain origin cuts selected) cutter < t * total origin cutter
  · simp only [firstSource, firstDeficit, firstFill, hf, decide_true, ite_true, hcomp]
    constructor
    · nlinarith
    constructor
    · linarith
    · nlinarith
  · simp only [firstSource, firstDeficit, firstFill, hf, decide_false, Bool.false_eq_true, ite_false]
    refine ⟨?_, mul_pos ht hM, le_of_not_gt hf⟩
    exact (mul_pos ht hM).trans_le (le_of_not_gt hf)

theorem firstSource_positive (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells)) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < (μ cutter).real (domain (firstSource origin cutter cuts selected t).cells) := by
  rw [← total_correct μ _ (firstSource_wellFormed μ origin hgood cutter cuts selected t)]
  exact (first_source_supply μ origin hgood cutter hpositive cuts selected t ht ht1).1

theorem firstAmount_value (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells)) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (firstAmount origin cutter cuts selected t : ℝ) = firstDeficit origin cutter cuts selected t /
      total (firstSource origin cutter cuts selected t) cutter := by
  have hs := first_source_supply μ origin hgood cutter hpositive cuts selected t ht ht1
  unfold firstAmount
  rw [amount_eq_fraction _ _ hs.2.1.le hs.2.2 hs.1]
  rfl

theorem firstCircular_mass (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells)) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (start : Circle) :
    (μ cutter).real (firstCircular policy origin cutter cuts selected t start) =
      firstDeficit origin cutter cuts selected t := by
  have hw := firstSource_wellFormed μ origin hgood cutter cuts selected t
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  unfold firstCircular
  rw [actual_prefix_mass μ policy hpolicy _ hw cutter hs (by decide) _ (by rfl) (by rfl)]
  change (firstAmount origin cutter cuts selected t : ℝ) * (μ cutter).real
    (domain (firstSource origin cutter cuts selected t).cells) = _
  rw [firstAmount_value μ origin hgood cutter hpositive cuts selected t ht ht1,
    total_correct μ _ hw, div_mul_cancel₀ _ hs.ne']

theorem firstCircular_signed_expectation (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells)) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (signed : SignedMeasure ℝ) :
    (∫ start, signed (firstCircular policy origin cutter cuts selected t start) ∂(volume : Measure Circle)) =
      (firstAmount origin cutter cuts selected t : ℝ) * signed (domain (firstSource origin cutter cuts selected t).cells) :=
  actual_prefix_signed_expectation μ policy hpolicy hmeas _
    (firstSource_wellFormed μ origin hgood cutter cuts selected t) cutter
    (firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1) (by decide) _
    (by rfl) (by rfl) signed 1

end EnvyFreeResearch.Full.UpperSnapshotSmall
