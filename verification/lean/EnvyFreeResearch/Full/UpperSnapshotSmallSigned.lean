import EnvyFreeResearch.Full.UpperSnapshotSmallCircle
import EnvyFreeResearch.Full.UpperSnapshotCandidatesSmall
import EnvyFreeResearch.Full.UpperLogicalPreparationState
import EnvyFreeResearch.Full.UpperLogicalCellNull

/-! The immutable signed interpolant as an actual finite signed measure.
Degenerate logical cells carry zero atomless row mass, so the construction
has exact cell scores without an absolute-continuity assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperEnvelope UpperLogicalPreparation UpperLogicalCells UpperRecordedDomain
variable {Cell : Type*} [Fintype Cell]

def signedEstimate (score : Cell → ℝ) (cells : Cell → Set ℝ) : SignedMeasure ℝ :=
  ∑ e, score e • (cond volume (cells e)).toSignedMeasure

def positiveIndices (score : Cell → ℝ) : Finset Cell := Finset.univ.filter (fun e => 0 < score e)

theorem signedEstimate_apply (score : Cell → ℝ) (cells : Cell → Set ℝ) (C : Set ℝ) (hC : MeasurableSet C) :
    signedEstimate score cells C = ∑ e, score e * (cond volume (cells e)).real C := by
  simp only [signedEstimate, _root_.sum_apply, _root_.smul_apply,
    Measure.toSignedMeasure_apply_measurable hC, smul_eq_mul]

theorem signedEstimate_bound (score : Cell → ℝ) (cells : Cell → Set ℝ) (hsum : ∑ e, score e = 0)
    (C : Set ℝ) (hC : MeasurableSet C) : |signedEstimate score cells C| ≤ (∑ e, |score e|) / 2 := by
  rw [signedEstimate_apply score cells C hC]
  exact UpperSnapshotCandidates.convex_signed_bound score _ hsum
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)

theorem signedEstimate_cell (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (hmeas : ∀ e, MeasurableSet (cells e)) (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (hfinite : ∀ e, volume (cells e) ≠ ∞) (hzero : ∀ e, volume (cells e) = 0 → score e = 0) (j : Cell) :
    signedEstimate score cells (cells j) = score j := by
  rw [signedEstimate_apply score cells _ (hmeas j)]
  classical
  rw [Finset.sum_eq_single j]
  · by_cases hz : volume (cells j) = 0
    · rw [hzero j hz, zero_mul]
    · have hs : (cond volume (cells j)).real (cells j) = 1 := by
        rw [measureReal_def, cond_apply_self hz (hfinite j), ENNReal.toReal_one]
      rw [hs, mul_one]
  · intro e _ hej
    have hz : (cond volume (cells e)).real (cells j) = 0 := by
      rw [measureReal_def, cond_apply (hmeas e), (hdis hej).inter_eq, measure_empty, mul_zero, ENNReal.toReal_zero]
    rw [hz, mul_zero]
  · simp

theorem signedEstimate_total (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (hmeas : ∀ e, MeasurableSet (cells e)) (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (hfinite : ∀ e, volume (cells e) ≠ ∞) (hzero : ∀ e, volume (cells e) = 0 → score e = 0)
    (U : Set ℝ) (hcover : (⋃ e, cells e) = U) :
    signedEstimate score cells U = ∑ e, score e := by
  rw [← hcover, VectorMeasure.of_disjoint_iUnion hmeas hdis, tsum_fintype]
  exact Finset.sum_congr rfl (fun e _ => signedEstimate_cell score cells hmeas hdis hfinite hzero e)

theorem selectedUnion_eq_biUnion (cells : Cell → Set ℝ) (selected : Finset Cell) :
    selectedUnion cells selected = ⋃ e ∈ selected, cells e := by
  ext x
  simp only [mem_selectedUnion, mem_iUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    exact ⟨e, he, hx⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨e, he, hx⟩

theorem signedEstimate_positive (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (hmeas : ∀ e, MeasurableSet (cells e)) (hdis : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (hfinite : ∀ e, volume (cells e) ≠ ∞) (hzero : ∀ e, volume (cells e) = 0 → score e = 0)
    (hsum : ∑ e, score e = 0) :
    signedEstimate score cells (selectedUnion cells (positiveIndices score)) = (∑ e, |score e|) / 2 := by
  rw [selectedUnion_eq_biUnion, VectorMeasure.of_biUnion_finset
    (fun i _ j _ hij => hdis hij) (fun i _ => hmeas i)]
  simp_rw [signedEstimate_cell score cells hmeas hdis hfinite hzero]
  rw [positiveIndices, Finset.sum_filter]
  calc
    _ = ∑ e, max (score e) 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : 0 < score e
      · simp only [he, ite_true, max_eq_left he.le]
      · simp only [he, ite_false, max_eq_right (le_of_not_gt he)]
    _ = _ := UpperSnapshotCandidates.positive_mass score hsum

theorem signedEstimate_contrast_bound (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (hsum : ∑ e, score e = 0) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    signedEstimate score cells A - signedEstimate score cells B ≤ ∑ e, |score e| := by
  have h1 := signedEstimate_bound score cells hsum A hA
  have h2 := signedEstimate_bound score cells hsum B hB
  have h1' := (abs_le.mp h1).2
  have h2' := (abs_le.mp h2).1
  linarith

/-- Scores read from actual normalized atomless row masses vanish on every
zero-volume logical cell, including cells crossing old physical joins. -/
theorem logical_score_null {m : ℕ} (μ ν : Measure ℝ) [NullSingletonClass μ] [NullSingletonClass ν]
    (cs : List Component) (cuts : Fin (m + 2) → ℝ) (r s : ℝ) (e : Fin (m + 1))
    (hz : volume (cell (domain cs) cuts e) = 0) :
    μ.real (cell (domain cs) cuts e) / r - ν.real (cell (domain cs) cuts e) / s = 0 := by
  simp only [measureReal_def, UpperLogicalCellNull.cell_null μ cs cuts e hz,
    UpperLogicalCellNull.cell_null ν cs cuts e hz, ENNReal.toReal_zero, zero_div, sub_self]

end EnvyFreeResearch.Full.UpperSnapshotSmall
