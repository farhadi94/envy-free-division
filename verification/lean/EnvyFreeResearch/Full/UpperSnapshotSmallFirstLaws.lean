import EnvyFreeResearch.Full.UpperSnapshotSmallFirstGeometry
import EnvyFreeResearch.Full.UpperSnapshotSmallFirstMeasurable
import EnvyFreeResearch.Full.UpperSnapshotCandidatesSmall

/-! Exact physical and signed laws for the first actual candidate stage. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ}

theorem firstCircular_measurableSet (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle) :
    MeasurableSet (firstCircular policy origin cutter cuts selected t start) :=
  prefix_measurable (by decide : 0 < 2) _ (domain_measurable _) _ _ _ _

theorem firstCircular_disjoint_positive (policy : Policy n) (origin : State n)
    (hdis : DisjointComponents origin.cells) (cutter : Fin n) (cuts : Fin (m + 2) → ℝ)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (start : Circle)
    (hfill : firstFill origin cutter cuts selected t = true) :
    Disjoint (domain (retain origin cuts selected).cells) (firstCircular policy origin cutter cuts selected t start) := by
  rw [firstCircular_restrict policy origin hdis, hfill, ite_eq_left rfl]
  exact disjoint_sdiff_right.mono_right inter_subset_left

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
include hpolicy hgood hpositive hzero hmono hsep ht ht1

theorem firstEndowment_mass (start : Circle) :
    (μ cutter).real (domain (firstEndowment policy origin cutter cuts selected t start).cells) =
      t * (μ cutter).real (domain origin.cells) := by
  rw [firstEndowment_domain policy origin hgood.2.1 cutter cuts hzero hmono hsep]
  by_cases hf : firstFill origin cutter cuts selected t = true
  · rw [hf, ite_eq_left rfl, measureReal_union
      (firstCircular_disjoint_positive policy origin hgood.2.1 cutter cuts selected t start hf)
      (firstCircular_measurableSet policy origin cutter cuts selected t start),
      firstCircular_mass μ policy hpolicy origin hgood cutter hpositive cuts selected t ht ht1]
    rw [firstDeficit, hf, ite_eq_left rfl, total_correct μ origin hgood,
      total_correct μ _ (retain_wellFormed μ origin hgood cuts selected)]
    ring
  · rw [ite_eq_right hf, firstCircular_mass μ policy hpolicy origin hgood cutter hpositive cuts selected t ht ht1]
    rw [firstDeficit, ite_eq_right hf, total_correct μ origin hgood]

theorem firstRemainder_mass (start : Circle) :
    (μ cutter).real (domain (firstRemainder policy origin cutter cuts selected t start).cells) =
      (1 - t) * (μ cutter).real (domain origin.cells) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  rw [(first_partition μ policy hpolicy origin hgood cutter cuts selected t hs start).2.2]
  have hsub : domain (firstEndowment policy origin cutter cuts selected t start).cells ⊆ domain origin.cells := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    have hmem := (List.mem_filter.mp hc).1
    have hfull := mem_domain.mpr ⟨c, hmem, hxc⟩
    rwa [firstRestored_domain] at hfull
  rw [measureReal_sdiff hsub (domain_measurable _),
    firstEndowment_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1]
  ring

theorem firstRemainder_positive (start : Circle) :
    0 < (μ cutter).real (domain (firstRemainder policy origin cutter cuts selected t start).cells) := by
  rw [firstRemainder_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1]
  exact mul_pos (sub_pos.mpr ht1) hpositive

omit hpolicy hpositive hzero hmono hsep ht ht1 in
theorem firstSource_total :
    total (firstSource origin cutter cuts selected t) cutter =
      if firstFill origin cutter cuts selected t then total origin cutter - total (retain origin cuts selected) cutter
      else total (retain origin cuts selected) cutter := by
  rw [total_correct μ _ (firstSource_wellFormed μ origin hgood cutter cuts selected t),
    firstSource_domain origin hgood.2.1]
  split_ifs
  · rw [measureReal_sdiff (retain_subset origin cuts selected) (domain_measurable _),
      total_correct μ origin hgood, total_correct μ _ (retain_wellFormed μ origin hgood cuts selected)]
  · exact (total_correct μ _ (retain_wellFormed μ origin hgood cuts selected) _).symm

omit hpolicy hpositive ht ht1 in
theorem firstEndowment_signed_eq (signed : SignedMeasure ℝ) (start : Circle) :
    signed (domain (firstEndowment policy origin cutter cuts selected t start).cells) =
      if firstFill origin cutter cuts selected t then signed (domain (retain origin cuts selected).cells) +
        signed (firstCircular policy origin cutter cuts selected t start)
      else signed (firstCircular policy origin cutter cuts selected t start) := by
  rw [firstEndowment_domain policy origin hgood.2.1 cutter cuts hzero hmono hsep]
  split_ifs with hf
  · exact VectorMeasure.of_union
      (firstCircular_disjoint_positive policy origin hgood.2.1 cutter cuts selected t start hf)
      (domain_measurable _) (firstCircular_measurableSet policy origin cutter cuts selected t start)
  · rfl

variable (hmeas : MeasurablePolicy policy)
include hmeas

omit hpolicy hpositive ht ht1 in
theorem firstEndowment_signed_integrable (signed : SignedMeasure ℝ) :
    Integrable (fun start => signed (domain (firstEndowment policy origin cutter cuts selected t start).cells))
      (volume : Measure Circle) := by
  have hc : Integrable (fun start => signed (firstCircular policy origin cutter cuts selected t start))
      (volume : Measure Circle) := actual_prefix_signed_integrable policy hmeas _ cutter (by decide) _ signed 1
  have heq := funext (firstEndowment_signed_eq μ policy origin hgood cutter cuts hzero hmono hsep selected t signed)
  rw [heq]
  by_cases hf : firstFill origin cutter cuts selected t = true
  · simp only [hf, ite_true]
    exact (integrable_const _).add hc
  · simp only [hf, ite_false]
    exact hc

theorem firstEndowment_signed_expectation (signed : SignedMeasure ℝ) :
    (∫ start, signed (domain (firstEndowment policy origin cutter cuts selected t start).cells)
      ∂(volume : Measure Circle)) =
      if firstFill origin cutter cuts selected t then signed (domain (retain origin cuts selected).cells) +
        (firstAmount origin cutter cuts selected t : ℝ) * signed (domain (firstSource origin cutter cuts selected t).cells)
      else (firstAmount origin cutter cuts selected t : ℝ) * signed (domain (firstSource origin cutter cuts selected t).cells) := by
  have hc : Integrable (fun start => signed (firstCircular policy origin cutter cuts selected t start))
      (volume : Measure Circle) := actual_prefix_signed_integrable policy hmeas _ cutter (by decide) _ signed 1
  have heq := funext (firstEndowment_signed_eq μ policy origin hgood cutter cuts hzero hmono hsep selected t signed)
  rw [heq]
  by_cases hf : firstFill origin cutter cuts selected t = true
  · simp only [hf, ite_true]
    rw [integral_add (integrable_const _) hc, integral_const, probReal_univ, one_smul,
      firstCircular_signed_expectation μ policy hpolicy hmeas origin hgood cutter hpositive cuts selected t ht ht1]
  · simp only [hf, ite_false]
    exact firstCircular_signed_expectation μ policy hpolicy hmeas origin hgood cutter hpositive cuts selected t ht ht1 signed

/-- Both manuscript first-piece mean formulas are derived from the actual
recorded candidate in the original oracle units. -/
theorem firstEndowment_mean (signed : SignedMeasure ℝ) (D : ℝ)
    (hwhole : signed (domain origin.cells) = 0)
    (hpos : signed (domain (retain origin cuts selected).cells) = D / 2) :
    (∫ start, signed (domain (firstEndowment policy origin cutter cuts selected t start).cells)
      ∂(volume : Measure Circle)) =
      UpperSnapshotCandidates.firstMean D t (total (retain origin cuts selected) cutter / total origin cutter) := by
  have hM : 0 < total origin cutter := by rw [total_correct μ origin hgood]; exact hpositive
  have hs := first_source_supply μ origin hgood cutter hpositive cuts selected t ht ht1
  rw [firstEndowment_signed_expectation μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
    selected t ht ht1 hmeas, firstAmount_value μ origin hgood cutter hpositive cuts selected t ht ht1,
    firstSource_total μ origin hgood cutter cuts selected t, firstSource_domain origin hgood.2.1,
    hpos]
  have hsig : signed (domain origin.cells \ domain (retain origin cuts selected).cells) = -(D / 2) := by
    rw [VectorMeasure.of_sdiff (domain_measurable _) (domain_measurable _) (retain_subset origin cuts selected), hwhole, hpos]
    ring
  by_cases hf : total (retain origin cuts selected) cutter < t * total origin cutter
  · have hratio : ¬t ≤ total (retain origin cuts selected) cutter / total origin cutter := by
      rw [le_div_iff₀ hM]
      exact not_le.mpr hf
    simp only [firstFill, hf, decide_true, ite_true, firstDeficit, hsig,
      UpperSnapshotCandidates.firstMean, hratio, ite_false]
    have hden : total origin cutter - total (retain origin cuts selected) cutter ≠ 0 := by
      have h := hs.1
      rw [firstSource_total μ origin hgood cutter cuts selected t] at h
      simpa only [firstFill, hf, decide_true, ite_true] using h.ne'
    field_simp
    <;> ring
  · have hratio : t ≤ total (retain origin cuts selected) cutter / total origin cutter :=
      (le_div_iff₀ hM).mpr (le_of_not_gt hf)
    simp only [firstFill, hf, decide_false, Bool.false_eq_true, ite_false, firstDeficit,
      UpperSnapshotCandidates.firstMean, hratio, ite_true, hpos]
    have hP : total (retain origin cuts selected) cutter ≠ 0 :=
      ne_of_gt ((mul_pos ht hM).trans_le (le_of_not_gt hf))
    field_simp
    <;> ring

end EnvyFreeResearch.Full.UpperSnapshotSmall
