import EnvyFreeResearch.Full.RefinedUpperPreparationExecution

/-! Exact physical witness masses and factor-two discrepancy guarantees. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperRecordedQuantiles UpperLogicalIsolation Chores
open scoped Classical unitInterval
variable {n k : ℕ} [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem dataWeights_physical (q m L : ℕ) (draw : Fin m → Fin k × I)
    (job : Job k) (a : Fin L) (i : Fin k) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    dataWeights active origin data L job a i =
      (μ (active i)).real (UpperGridMerge.logicalCells policy active origin q m draw
        (dataChosen active origin data L job a)) /
      (μ (active i)).real (domain (dataRetained active origin data L).cells) := by
  dsimp only
  unfold dataWeights coreWeights
  change multipliers active origin _ i * UpperGridCache.table policy active origin q m draw i
    (dataChosen active origin _ L job a) = _
  unfold multipliers
  rw [dataRetained_execute]
  rw [total_correct μ origin hgood,
    total_correct μ _ (retainedState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw _),
    UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
  field_simp [(hpositive i).ne']

theorem dataWeights_gap (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) (job : Job k) (a : Fin L) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    dataDisagreement active origin data L job.1.1.1 job.1.1.2 / 2 ≤
      |dataWeights active origin data L job a job.1.1.1 -
        dataWeights active origin data L job a job.1.1.2| := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  have hs := dataResult_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  have he : RefinedUpperPeeling.run (UpperGridCache.table policy active origin q m draw)
      (UpperRecordedParents.parent policy active origin q m draw)
      (List.ofFn (fun i : Fine k q m => i)) (requests k L) ∅ =
      some (dataResult active origin data L) := hs.1
  dsimp only
  rw [dataDisagreement,dataRetained_execute]
  change UpperPayments.cellGap (UpperCorrectionSetup.table active
    (reserveState policy active origin q m draw 0 (retentionLabels (dataResult active origin data L).2))
    (UpperGridMerge.cuts policy active origin q m draw)) _ _ / 2 ≤ _
  rw [reserve_cellGap μ policy hpolicy active origin hgood hpositive]
  apply picked_controls_reserve _
    (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    _ _ _ UpperPreparedIsolation.rows ∅ _ (dataResult active origin data L).2 he hs.2.1 0 _
    (fun c hc => ⟨List.mem_ofFn.mpr ⟨c,rfl⟩,?_⟩) (job,a)
  simpa only [reserveCells,Finset.mem_filter,Finset.mem_univ,true_and,retentionLabels_le_zero] using hc

theorem dataWeights_nonneg (q m L : ℕ) (draw : Fin m → Fin k × I)
    (job : Job k) (a : Fin L) (i : Fin k) :
    0 ≤ dataWeights active origin (UpperGridMerge.prepare policy active origin q m draw) L job a i := by
  rw [dataWeights_physical μ policy hpolicy active origin hgood hpositive]
  exact div_nonneg measureReal_nonneg measureReal_nonneg

theorem dataWeights_small (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(jobCount k*L) ≤ q+1) (job : Job k) (a : Fin L) (i : Fin k) :
    dataWeights active origin (UpperGridMerge.prepare policy active origin q m draw) L job a i ≤ 2/(q+1 : ℝ) := by
  rw [dataWeights_physical μ policy hpolicy active origin hgood hpositive]
  have hhalf := dataRetained_half μ policy hpolicy active origin hgood hpositive q m L draw hbudget i
  have hT : 0 < (μ (active i)).real (domain (dataRetained active origin
      (UpperGridMerge.prepare policy active origin q m draw) L).cells) :=
    (div_pos (hpositive i) (by norm_num : (0 : ℝ) < 2)).trans_le hhalf
  have hsmall := (div_le_iff₀ (hpositive i)).mp
    (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw i
      (dataChosen active origin (UpperGridMerge.prepare policy active origin q m draw) L job a))
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ (1/(q+1 : ℝ))*(μ (active i)).real (domain origin.cells) := hsmall
    _ ≤ (1/(q+1 : ℝ))*(2*(μ (active i)).real (domain (dataRetained active origin
        (UpperGridMerge.prepare policy active origin q m draw) L).cells)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end EnvyFreeResearch.Full.RefinedUpperPreparation
