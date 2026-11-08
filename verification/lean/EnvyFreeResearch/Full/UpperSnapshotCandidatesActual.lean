import EnvyFreeResearch.Full.UpperSnapshotCandidatesRecorded

/-! The actual recorded quantile-plus-sample grid satisfies every input
check of the large-disagreement candidate, without a new oracle call. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalCells UpperDomainDifference
  UpperCircularStage UpperStageMeasurable UpperCommonGrid Chores
variable {n k : ℕ}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive

/-- The grid cache cap is the original-unit cap for every literal logical
cell, including those with internal physical joins. -/
theorem recorded_cell_small (q m : ℕ) (draw : Fin m → Fin k × I) (i : Fin k)
    (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)) :
    (μ (active i)).real (cell (domain (UpperGridCache.aligned policy active origin q m draw).cells)
      (UpperGridMerge.cuts policy active origin q m draw) e) ≤
        (1 / (q + 1 : ℝ)) * (μ (active i)).real (domain (UpperGridCache.aligned policy active origin q m draw).cells) := by
  have h := UpperGridCache.table_small μ policy hpolicy active origin hgood hpositive q m draw i e
  rw [UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive] at h
  have hr := (div_le_iff₀ (hpositive i)).mp h
  simpa only [UpperGridMerge.logicalCells, UpperGridCache.aligned_domain] using hr

/-- Complete recorded partition and simultaneous physical near-EF checks.
Only positivity of the selected disagreement chooses this branch; its grid
and cell inequalities are proved from the actual query executor. -/
theorem recorded_large_ready (hk : 2 ≤ k) (q m : ℕ) (draw : Fin m → Fin k × I) (cutter : Fin k)
    (tau : ℝ) (htau : 0 ≤ tau) (hquarter : (1 / (q + 1 : ℝ)) ≤ 1 / 4)
    (hscale : (1 / (q + 1 : ℝ)) ≤ tau / 2)
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin (UpperGridMerge.prepare policy active origin q m draw)) cutter) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let old := candidateOld (by omega) active origin data cutter
    let buffer := candidateBuffer (by omega) active origin data cutter
    (∀ j, WellFormed μ (old j)) ∧ WellFormed μ buffer ∧
    Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)) ∧
    (∀ j, Disjoint (domain (old j).cells) (domain buffer.cells)) ∧
    (⋃ j, domain (old j).cells) ∪ domain buffer.cells = domain origin.cells ∧
    ∀ i, (μ (active i)).real (domain origin.cells) / 2 ≤ (μ (active i)).real (domain buffer.cells) ∧
      0 < (μ (active i)).real (domain buffer.cells) ∧
      ∀ j h, |(μ (active i)).real (domain (old j).cells) - (μ (active i)).real (domain (old h).cells)| ≤
        tau * (μ (active i)).real (domain buffer.cells) := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let state := UpperGridData.aligned data
  let cuts := UpperGridData.cuts data
  let values := UpperGridData.table active origin data
  let F := candidatePositive (by omega) active origin data cutter
  let G := candidateNegative (by omega) active origin data cutter
  have hnormal (i : Fin k) : ∑ e, values i e = 1 :=
    UpperGridCache.table_normalized μ policy hpolicy active origin hgood hpositive q m draw i
  have hFG : F ≠ G := (selected_signed_cells (by omega) values cutter hnormal hD).2.2
  have hstate : WellFormed μ state := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hdom : domain state.cells = domain origin.cells := UpperGridCache.aligned_domain policy active origin q m draw
  have hz : cuts 0 = 0 := (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  have ho : cuts (Fin.last (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)) = 1 :=
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).2
  have hm : Monotone cuts := grid_monotone _
  have hs : ∀ e, SeparatedAt (cuts e) state.cells := UpperGridCache.aligned_separated policy active origin q m draw
  have hp := large_partition hk state cuts hz ho hm hs F G hFG
  refine ⟨fun j => largeEndowment_wellFormed μ state hstate cuts F G j,
    largeBuffer_wellFormed μ state hstate cuts F G, hp.1, hp.2.1, hp.2.2.trans hdom, ?_⟩
  intro i
  have hc := large_near_checks (k := k) (μ (active i)) state cuts hz ho hm hs F G hFG (1 / (q + 1 : ℝ)) tau
    (by positivity) hquarter htau hscale (by rw [hdom]; exact hpositive i)
    (recorded_cell_small μ policy hpolicy active origin hgood hpositive q m draw i)
  rw [hdom] at hc
  exact hc

/-- Exact physical values of the first and second old labels, and the empty
third label required by the large-branch contrast comparison. -/
theorem recorded_large_values (hk : 3 ≤ k) (q m : ℕ) (draw : Fin m → Fin k × I) (cutter i : Fin k) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let values := UpperGridData.table active origin data
    let old := candidateOld (by omega) active origin data cutter
    (μ (active i)).real (domain (old ⟨0, by omega⟩).cells) / (μ (active i)).real (domain origin.cells) =
        values i (candidatePositive (by omega) active origin data cutter) ∧
      (μ (active i)).real (domain (old ⟨1, by omega⟩).cells) / (μ (active i)).real (domain origin.cells) =
        values i (candidateNegative (by omega) active origin data cutter) ∧
      domain (old ⟨2, by omega⟩).cells = ∅ := by
  have hz := (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  have hs := UpperGridCache.aligned_separated policy active origin q m draw
  have he (j : Fin k) := largeEndowment_domain (UpperGridCache.aligned policy active origin q m draw)
    (UpperGridMerge.cuts policy active origin q m draw) hz (grid_monotone _) hs
    (candidatePositive (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter)
    (candidateNegative (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter) j
  simp only [UpperGridCache.aligned_domain] at he
  constructor
  · rw [candidateOld, UpperGridData.aligned_execute, UpperGridData.cuts_execute, he ⟨0, by omega⟩]
    simp only [ite_true]
    exact (UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m draw i _).symm
  constructor
  · rw [candidateOld, UpperGridData.aligned_execute, UpperGridData.cuts_execute, he ⟨1, by omega⟩]
    simp only [Nat.one_ne_zero, ite_false, ite_true]
    exact (UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m draw i _).symm
  · rw [candidateOld, UpperGridData.aligned_execute, UpperGridData.cuts_execute, he ⟨2, by omega⟩]
    norm_num

end EnvyFreeResearch.Full.UpperSnapshotCandidates
