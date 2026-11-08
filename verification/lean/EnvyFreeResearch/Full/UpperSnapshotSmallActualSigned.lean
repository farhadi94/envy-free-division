import EnvyFreeResearch.Full.UpperSnapshotSmallSigned
import EnvyFreeResearch.Full.UpperLogicalPreparationState

/-! The signed interpolant and the physically retained positive logical cells
refer to the same immutable recorded partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperLogicalCells UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperGridRecords UpperDomainDifference
variable {n m : ℕ}

theorem logical_interpolant_facts (origin : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hlast : cuts (Fin.last (m + 1)) = 1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells) (score : Fin (m + 1) → ℝ)
    (hsum : ∑ e, score e = 0)
    (hnull : ∀ e, volume (cell (domain origin.cells) cuts e) = 0 → score e = 0) :
    signedEstimate score (cell (domain origin.cells) cuts) (domain origin.cells) = 0 ∧
    signedEstimate score (cell (domain origin.cells) cuts)
      (domain (retain origin cuts (positiveIndices score)).cells) = (∑ e, |score e|)/2 := by
  have hm := cell_measurable (domain origin.cells) (domain_measurable origin.cells) cuts
  have hd := cells_disjoint (domain origin.cells) cuts hmono
  have hf (e : Fin (m + 1)) : volume (cell (domain origin.cells) cuts e) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono ((cell_subset _ _ e).trans (domain_subset_unit _))).trans_lt
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) 1) < ∞)
  have hc := cells_cover (domain origin.cells) cuts hmono
    (by simpa only [hzero, hlast] using domain_subset_unit origin.cells)
  constructor
  · rw [signedEstimate_total score _ hm hd hf hnull _ hc, hsum]
  · rw [retain_domain origin cuts hzero hmono hsep]
    exact signedEstimate_positive score _ hm hd hf hnull hsum

end EnvyFreeResearch.Full.UpperSnapshotSmall
