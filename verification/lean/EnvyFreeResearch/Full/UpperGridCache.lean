import EnvyFreeResearch.Full.UpperGridMerge
import EnvyFreeResearch.Full.UpperGridCells

/-!
# The complete recorded normalized logical-cell table

This is the table consumed by finite Repair computations. It is computed by
summing recorded physical components and dividing by recorded original-buffer
masses. The physical profile enters only the proof that these computations
are exactly normalized logical-cell masses.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval BigOperators

namespace EnvyFreeResearch.Full.UpperGridCache

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridRecords
  UpperGridCells UpperLogicalCells UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperCommonGrid Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def aligned (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : State n := align (UpperGridMerge.prepare policy active origin q m draw).2.2

def table (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (a : Agent) (i : Fin (count (Agent := Agent) q + m + 1)) : ℝ :=
  cachedMass (aligned policy active origin q m draw) (UpperGridMerge.cuts policy active origin q m draw)
    (active a) i / total origin (active a)

theorem aligned_domain (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : domain (aligned policy active origin q m draw).cells = domain origin.cells := by
  rw [aligned, align_domain, UpperGridMerge.prepare_domain]

/-- Every merged logical boundary separates the actual physical atoms,
including both resource bounds and all repeated sampled endpoints. -/
theorem aligned_separated (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (j : Fin (count (Agent := Agent) q + m + 2)) :
    SeparatedAt (UpperGridMerge.cuts policy active origin q m draw j) (aligned policy active origin q m draw).cells := by
  let coarse := UpperRecordedQuantiles.run policy active origin q
  let sampled := UpperRecordedGrid.execute policy active coarse.2 m draw
  let points := Fin.append coarse.1 sampled.1
  have hcoarse (i : Fin (count (Agent := Agent) q)) : SeparatedAt (coarse.1 i) sampled.2.cells := by
    have hc : SeparatedAt (coarse.1 i) coarse.2.cells := by
      change SeparatedAt (coarse.1 i) (refineEndpoints origin.cells (List.ofFn coarse.1))
      exact refineEndpoints_separated _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change SeparatedAt (coarse.1 i) (refineEndpoints coarse.2.cells (List.ofFn sampled.1))
    exact refineEndpoints_preserves_separated _ _ _ hc
  have hsample (i : Fin m) : SeparatedAt (sampled.1 i) sampled.2.cells := by
    change SeparatedAt (sampled.1 i) (refineEndpoints coarse.2.cells (List.ofFn sampled.1))
    exact refineEndpoints_separated _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hpoint (i : Fin (count (Agent := Agent) q + m)) :
      SeparatedAt (points i) (aligned policy active origin q m draw).cells := by
    have hp : SeparatedAt (points i) sampled.2.cells := by
      refine Fin.addCases ?_ ?_ i
      · intro r
        simpa only [points, Fin.append_left] using hcoarse r
      · intro r
        simpa only [points, Fin.append_right] using hsample r
    exact refineAt_preserves_separated 1 _ _ (refineAt_preserves_separated 0 _ _ hp)
  have hraw (i : Fin (count (Agent := Agent) q + m + 2)) :
      SeparatedAt (raw points i) (aligned policy active origin q m draw).cells := by
    refine Fin.lastCases ?_ (fun r => ?_) i
    · simpa only [raw, Fin.snoc_last, aligned, UpperGridMerge.prepare, sampled, coarse] using align_separated_one sampled.2
    · refine Fin.cases ?_ (fun r => ?_) r
      · simpa only [raw, Fin.snoc_castSucc, Fin.cons_zero, aligned, UpperGridMerge.prepare, sampled, coarse] using align_separated_zero sampled.2
      · simpa only [raw_endpoint] using hpoint r
  exact hraw (UpperSortedGrid.select (raw points) j)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem aligned_wellFormed (q m : ℕ) (draw : Fin m → Agent × I) :
    WellFormed μ (aligned policy active origin q m draw) :=
  align_wellFormed μ _ (UpperGridMerge.prepare_wellFormed μ policy hpolicy active origin hgood hpositive q m draw)

/-- The actual finite cache contains exact normalized masses of the literal
logical cells, rather than a physical-component surrogate. -/
theorem table_correct (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (i : Fin (count (Agent := Agent) q + m + 1)) :
    table policy active origin q m draw a i =
      (μ (active a)).real (UpperGridMerge.logicalCells policy active origin q m draw i) /
        (μ (active a)).real (domain origin.cells) := by
  have hz := (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  unfold table
  rw [cachedMass_correct μ _ (aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw)
    _ hz (grid_monotone _) (aligned_separated policy active origin q m draw), aligned_domain,
    total_correct μ origin hgood]
  rfl

theorem table_nonneg (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (i : Fin (count (Agent := Agent) q + m + 1)) : 0 ≤ table policy active origin q m draw a i := by
  rw [table_correct μ policy hpolicy active origin hgood hpositive]
  exact div_nonneg measureReal_nonneg (hpositive a).le

theorem table_small (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (i : Fin (count (Agent := Agent) q + m + 1)) : table policy active origin q m draw a i ≤ 1 / (q + 1 : ℝ) := by
  rw [table_correct μ policy hpolicy active origin hgood hpositive]
  exact UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw a i

theorem table_normalized (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent) :
    (∑ i, table policy active origin q m draw a i) = 1 := by
  simp_rw [table_correct μ policy hpolicy active origin hgood hpositive]
  rw [← Finset.sum_div]
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  have hs := cell_mass_sum (μ (active a)) (domain origin.cells) (domain_measurable origin.cells)
    (UpperGridMerge.cuts policy active origin q m draw) (grid_monotone _) (by
      rw [he.1, he.2]
      exact domain_subset_unit origin.cells)
  rw [UpperGridMerge.logicalCells, hs]
  exact div_self (hpositive a).ne'

end Correctness

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem aligned_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) :
    Measurable (fun p : State n × (Fin m → Agent × I) => aligned policy active p.1 q m p.2) :=
  align_measurable.comp (measurable_snd.comp (measurable_snd.comp
    (UpperGridMerge.prepare_measurable policy hpolicy active q m)))

theorem table_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) (a : Agent)
    (i : Fin (count (Agent := Agent) q + m + 1)) :
    Measurable (fun p : State n × (Fin m → Agent × I) => table policy active p.1 q m p.2 a i) :=
  (cachedMass_measurable _ _ (aligned_measurable policy hpolicy active q m)
    (fun c => (measurable_pi_apply c).comp (UpperGridMerge.cuts_measurable policy hpolicy active q m))
    (active a) i).div (total_measurable _ _ measurable_fst measurable_const)

end Measurability

end EnvyFreeResearch.Full.UpperGridCache
