import EnvyFreeResearch.Full.UpperShrinkMedian

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperQueryPrograms
  UpperUnionSampling UpperGridRecords UpperSamplingRecords UpperEndpointCache

variable {n : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (state : State n) (hgood : WellFormed μ state) (cutter : Fin n)

include hpolicy hgood in
theorem median_wellFormed : WellFormed μ (median policy state cutter).2 := by
  unfold median
  split_ifs with hz
  · exact hgood
  · have ht := total_correct μ state hgood cutter
    have hp : 0 < (μ cutter).real (domain state.cells) := by rw [← ht]; exact lt_of_not_ge hz
    have hr := sampleExecution_all_records μ policy hpolicy state.history cutter (values state cutter)
      state.cells hgood.2.1 hgood.2.2.1 hgood.2.2.2 (values_correct μ state hgood cutter) hp half
    rw [← ht] at hr
    let result := sampleExecution policy state.history cutter (values state cutter) (total state cutter) state.cells half
    have hw : WellFormed μ (⟨state.cells, result.2⟩ : State n) :=
      ⟨hgood.1, hgood.2.1, hr.2.1, recordedHistory_mono _ hgood.2.2.2 hr.2.2.1⟩
    apply refineEndpoints_wellFormed μ _ hw [result.1]
    intro p hp
    have he : p = result.1 := by simpa using hp
    subst p
    exact hr.2.2.2

include hpolicy hgood in
theorem median_positive_endpoint (hp : 0 < (μ cutter).real (domain state.cells)) :
    ∃ x, (median policy state cutter).1 = some x ∧ x ∈ Icc (0 : ℝ) 1 ∧
      (μ cutter).real (domain state.cells ∩ Iic x) = (μ cutter).real (domain state.cells) / 2 := by
  have ht := total_correct μ state hgood cutter
  have hn : ¬total state cutter ≤ 0 := by rw [ht]; exact not_le_of_gt hp
  have hs := sampleExecution_spec μ policy hpolicy state.history cutter (values state cutter) state.cells
    hgood.1 hgood.2.1 (values_correct μ state hgood cutter) hp half (by norm_num [half])
  rw [← ht] at hs
  let result := sampleExecution policy state.history cutter (values state cutter) (total state cutter) state.cells half
  refine ⟨result.1, by simp only [median, hn, ite_false]; rfl, hs.1, ?_⟩
  have he := hs.2.1
  rw [normalized_cdf (μ cutter) (domain state.cells) hp result.1] at he
  change (μ cutter).real (domain state.cells ∩ Iic result.1) / (μ cutter).real (domain state.cells) = 1 / 2 at he
  have hm := (div_eq_iff hp.ne').mp he
  linarith

include hgood in
theorem median_zero (hz : (μ cutter).real (domain state.cells) = 0) :
    median policy state cutter = (none, state) := by
  simp only [median, total_correct μ state hgood cutter, hz, le_refl, ite_true]

end EnvyFreeResearch.Full.UpperShrink
