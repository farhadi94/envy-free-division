import EnvyFreeResearch.Full.UpperSnapshotCandidatesActual
import EnvyFreeResearch.Full.UpperSnapshotCandidatesContrast

/-! The old-label contrast for the actual recorded large candidate, using
cached reserve normalizers and the proved upper-mass check. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalCells UpperDomainDifference
  UpperCircularStage UpperStageMeasurable UpperCommonGrid UpperLogicalIsolation UpperSnapshotContrast Chores
variable {n k coarse fine : ℕ}

def candidateNormalizers (active : Fin k → Fin n) (origin reserve : State n) (i : Fin k) : ℝ :=
  total reserve (active i) / total origin (active i)

def candidateChoice (hk : 3 ≤ k) (active : Fin k → Fin n) (origin : State n)
    (data : UpperGridData.Data n coarse fine) (cutter : Fin k) (reserve : State n) : (Fin k × Fin k) × (Fin k × Fin k) :=
  largeSelection hk (selectedRow (by omega) (UpperGridData.table active origin data) cutter) cutter
    (candidateNormalizers active origin reserve)

theorem double_normalization (a u r : ℝ) (hu : u ≠ 0) (hr : r ≠ 0) :
    a / r = (a / u) / (r / u) := by field_simp

variable {X : Type*} [MeasurableSpace X]

theorem candidateChoice_measurable (hk : 3 ≤ k) (active : Fin k → Fin n) (origin reserve : X → State n)
    (data : X → UpperGridData.Data n coarse fine) (cutter : Fin k)
    (horigin : Measurable origin) (hreserve : Measurable reserve) (hdata : Measurable data) :
    Measurable (fun x => candidateChoice hk active (origin x) (data x) cutter (reserve x)) :=
  largeSelection_measurable hk _ cutter _
    (selectedRow_measurable (by omega) _ cutter (UpperGridData.table_measurable active origin data horigin hdata))
    (fun i => (total_measurable reserve (fun _ => active i) hreserve measurable_const).div
      (total_measurable origin (fun _ => active i) horigin measurable_const))

/-- After any fresh successful strengthened preparation, this explicit
cached choice supplies Snapshot's old-matrix contrast premise. -/
theorem recorded_candidate_contrast (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hk : 3 ≤ k) (q m : ℕ) (draw : Fin m → Fin k × I) (cutter : Fin k)
    (reserve : State n) (hreserve : WellFormed μ reserve)
    (hrespositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hupper : ∀ i, (μ (active i)).real (domain reserve.cells) ≤ 3 * theta / 2 *
      (μ (active i)).real (domain (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter).cells))
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin (UpperGridMerge.prepare policy active origin q m draw)) cutter) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let choice := candidateChoice hk active origin data cutter reserve
    selectedDistance (by omega) (UpperGridData.table active origin data) cutter /
        (3 * theta * (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1 : ℕ)) ≤
      contrast (oldMatrix active (candidateOld (by omega) active origin data cutter) reserve)
        choice.1.1 choice.1.2 choice.2.1 choice.2.2 := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let state := UpperGridData.aligned data
  let values := UpperGridData.table active origin data
  let old := candidateOld (by omega) active origin data cutter
  let F := candidatePositive (by omega) active origin data cutter
  let G := candidateNegative (by omega) active origin data cutter
  let r := candidateNormalizers active origin reserve
  have hstate : WellFormed μ state := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hold (j : Fin k) : WellFormed μ (old j) := largeEndowment_wellFormed μ state hstate _ F G j
  have hr (i : Fin k) : r i = (μ (active i)).real (domain reserve.cells) / (μ (active i)).real (domain origin.cells) := by
    exact congrArg₂ (· / ·) (total_correct μ reserve hreserve _) (total_correct μ origin hgood _)
  have hrpos (i : Fin k) : 0 < r i := by rw [hr]; exact div_pos (hrespositive i) (hpositive i)
  have hB : domain (candidateBuffer (by omega) active origin data cutter).cells ⊆ domain origin.cells := by
    simp only [candidateBuffer, data, UpperGridData.aligned_execute, UpperGridData.cuts_execute]
    rw [largeBuffer_domain _ _
      (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
      (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).2
      (grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw)]
    exact sdiff_subset.trans (by rw [UpperGridCache.aligned_domain])
  have hrupper (i : Fin k) : r i ≤ 3 * theta / 2 := by
    rw [hr]
    apply (div_le_iff₀ (hpositive i)).mpr
    exact (hupper i).trans (mul_le_mul_of_nonneg_left (measureReal_mono hB) (by positivity))
  have hv (i : Fin k) := recorded_large_values μ policy hpolicy active origin hgood hpositive hk q m draw cutter i
  have hfirst (i : Fin k) : oldMatrix active old reserve i ⟨0, by omega⟩ = values i F / r i := by
    rw [oldMatrix, total_correct μ _ (hold _), total_correct μ reserve hreserve]
    rw [double_normalization _ _ _ (hpositive i).ne' (hrespositive i).ne', (hv i).1, ← hr]
  have hsecond (i : Fin k) : oldMatrix active old reserve i ⟨1, by omega⟩ = values i G / r i := by
    rw [oldMatrix, total_correct μ _ (hold _), total_correct μ reserve hreserve]
    rw [double_normalization _ _ _ (hpositive i).ne' (hrespositive i).ne', (hv i).2.1, ← hr]
  have hempty (i : Fin k) : oldMatrix active old reserve i ⟨2, by omega⟩ = 0 := by
    rw [oldMatrix, total_correct μ _ (hold _), (hv i).2.2]
    simp only [measureReal_empty, zero_div]
  have hnormal (i : Fin k) : ∑ e, values i e = 1 := UpperGridCache.table_normalized μ policy hpolicy active origin hgood hpositive q m draw i
  have hs := selected_signed_cells (by omega) values cutter hnormal hD
  exact largeSelection_contrast hk values (selectedRow (by omega) values cutter) cutter F G (oldMatrix active old reserve) r
    hrpos theta (selectedDistance (by omega) values cutter) hD.le hrupper
    (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    hs.1 hs.2.1 hfirst hsecond hempty

end EnvyFreeResearch.Full.UpperSnapshotCandidates
