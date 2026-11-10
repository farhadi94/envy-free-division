import EnvyFreeResearch.Full.RefinedUpperStabilityProcedure
import EnvyFreeResearch.Full.UpperGridInterpolationPhysical

/-! The endpoint procedure is exactly the physically queried preparation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open MeasureTheory Set UpperGridInterpolation UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperLogicalCells Chores
open scoped Classical unitInterval
variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

def physicalCumulative (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (origin : State n)
    (a : Agent) (x : ℝ) : ℝ :=
  domainCumulative (μ (active a)) origin.cells x / (μ (active a)).real (domain origin.cells)

lemma physicalCumulative_measurable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Agent → Fin n) (origin : State n) (a : Agent) :
    Measurable (physicalCumulative μ active origin a) :=
  (domainCumulative_measurable (μ (active a)) origin.cells).div_const _

lemma physicalCumulative_monotone (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Agent → Fin n) (origin : State n) (a : Agent) :
    Monotone (physicalCumulative μ active origin a) := by
  intro x y hxy
  exact div_le_div_of_nonneg_right
    (domainCumulative_monotone (μ (active a)) origin.cells (measure_ne_top _ _) hxy) measureReal_nonneg

theorem recorded_table_pointValues (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (i : Fin (UpperRecordedQuantiles.count (Agent := Agent) q + m + 1)) :
    UpperGridCache.table policy active origin q m draw a i =
      pointValues (physicalCumulative μ active origin)
        (UpperGridMerge.cuts policy active origin q m draw) a i := by
  rw [UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive]
  unfold UpperGridMerge.logicalCells pointValues physicalCumulative
  rw [physical_cell_mass (μ (active a)) origin.cells (measure_ne_top _ _)
    (UpperGridMerge.cuts policy active origin q m draw) (UpperCommonGrid.grid_monotone _) i]
  exact sub_div _ _ _

/-- Equality of complete deterministic executions: the Borel endpoint
procedure uses the same actual fine-cell values, coarse parents, and ties
as the query-cache implementation. -/
theorem pointRun_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent)) :
    pointRun (physicalCumulative μ active origin)
      (UpperRecordedQuantiles.cuts policy active origin q) jobs
      (UpperGridMerge.cuts policy active origin q m draw) =
        representativeRun policy active origin q m draw jobs := by
  have hv : pointValues (physicalCumulative μ active origin)
      (UpperGridMerge.cuts policy active origin q m draw) =
        UpperGridCache.table policy active origin q m draw := by
    funext a i
    exact (recorded_table_pointValues μ policy hpolicy active origin hgood hpositive q m draw a i).symm
  have hp : pointParents (UpperRecordedQuantiles.cuts policy active origin q)
      (UpperGridMerge.cuts policy active origin q m draw) =
        UpperRecordedParents.parent policy active origin q m draw := by
    funext i
    exact (recorded_parent_interval μ policy hpolicy active origin hgood hpositive q m draw i).symm
  unfold pointRun representativeRun
  rw [hv,hp]
  rfl

end EnvyFreeResearch.Full.RefinedUpperPeeling
