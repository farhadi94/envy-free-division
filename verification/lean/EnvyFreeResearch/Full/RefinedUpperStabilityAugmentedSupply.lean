import EnvyFreeResearch.Full.RefinedUpperStabilitySupply

/-! The augmented stability experiment is a refinement of the actual
recorded coarse grid. Completion is derived without calling a test oracle. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperStability
open RefinedUpperPeeling UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperGridInterpolation UpperSortedGrid
variable {n : ℕ} {Row : Type*} [Fintype Row] [Nonempty Row]

theorem grid_eq_augmented {b m : ℕ} (permanent : Fin b → ℝ) (samples : Fin m → ℝ) :
    UpperCommonGrid.grid (Fin.append permanent samples) = sorted (augmented permanent samples) := by
  unfold UpperCommonGrid.grid UpperCommonGrid.raw augmented
  rw [Fin.cons_snoc_eq_snoc_cons]
  rfl

theorem inserted_recorded_run_completes
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Row → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Row × I) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1)
    (jobs : List (Row × Row)) (hbudget : 2 * jobs.length < q+1) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    ∃ pairs final, pointRun (physicalCumulative μ active origin)
      (UpperRecordedQuantiles.cuts policy active origin q) jobs
      (sorted (augmented data.1 (Fin.cons z data.2.1))) = some (pairs,final) ∧
      pairs.length = jobs.length ∧ final.card ≤ 2 * jobs.length := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  have hpermanent : ∀ i, data.1 i ∈ Icc (0 : ℝ) 1 :=
    UpperGridMerge.coarse_endpoints μ policy hp active origin hgood hpositive q
  have hsamples : ∀ i, (Fin.cons z data.2.1 : Fin (m+1) → ℝ) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    refine Fin.cases hz (fun i => ?_) i
    exact UpperGridMerge.sampled_endpoints μ policy hp active origin hgood hpositive q m draw i
  have hall : ∀ i, Fin.append data.1 (Fin.cons z data.2.1) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hpermanent j
    · simpa using hsamples j
  have h := recorded_refinement_completes μ policy hp active origin hgood hpositive q
    (UpperCommonGrid.grid (Fin.append data.1 (Fin.cons z data.2.1)))
    (UpperCommonGrid.grid_monotone _) (UpperCommonGrid.grid_first _ hall)
    (UpperCommonGrid.grid_last _ hall)
    (UpperGridMerge.grid_append_contains data.1 (Fin.cons z data.2.1) hpermanent hsamples)
    jobs hbudget
  simpa only [grid_eq_augmented] using h

end EnvyFreeResearch.Full.RefinedUpperStability
