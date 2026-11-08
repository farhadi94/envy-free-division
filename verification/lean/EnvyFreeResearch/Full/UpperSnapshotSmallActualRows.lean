import EnvyFreeResearch.Full.UpperSnapshotSmallActualSigned

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperLogicalCells UpperRecordedDomain UpperCorrectionExecution
variable {n m : ℕ}

/-- Both finite-row conditions for the actual normalized physical scores.
No assumption of a density or absolute continuity is used. -/
theorem normalized_physical_scores (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (origin : State n) (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0)
    (hlast : cuts (Fin.last (m + 1)) = 1) (hmono : Monotone cuts)
    (hμ : 0 < μ.real (domain origin.cells)) (hν : 0 < ν.real (domain origin.cells)) :
    (∑ e, (μ.real (cell (domain origin.cells) cuts e) / μ.real (domain origin.cells) -
      ν.real (cell (domain origin.cells) cuts e) / ν.real (domain origin.cells))) = 0 ∧
    (∀ e, volume (cell (domain origin.cells) cuts e) = 0 →
      μ.real (cell (domain origin.cells) cuts e) / μ.real (domain origin.cells) -
      ν.real (cell (domain origin.cells) cuts e) / ν.real (domain origin.cells) = 0) := by
  have hwithin : domain origin.cells ⊆ Icc (cuts 0) (cuts (Fin.last (m+1))) := by
    simpa only [hzero, hlast] using domain_subset_unit origin.cells
  constructor
  · rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      cell_mass_sum μ _ (domain_measurable _) cuts hmono hwithin,
      cell_mass_sum ν _ (domain_measurable _) cuts hmono hwithin,
      div_self hμ.ne', div_self hν.ne', sub_self]
  · intro e he
    exact logical_score_null μ ν origin.cells cuts _ _ e he

end EnvyFreeResearch.Full.UpperSnapshotSmall
