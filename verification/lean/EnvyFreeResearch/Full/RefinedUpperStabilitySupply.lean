import EnvyFreeResearch.Full.RefinedUpperStabilityRecordedProcedure
import EnvyFreeResearch.Full.RefinedUpperPeelingRecorded

/-! Query-free completion on any refinement of the recorded coarse grid,
including the grid obtained by inserting an independent test coordinate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalCells UpperGridInterpolation
variable {n a m : ℕ} {Row : Type*} [Fintype Row] [Nonempty Row]

theorem physical_pointRun_completes
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (origin : State n)
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse)
    (fine : Fin (m+2) → ℝ) (hf : Monotone fine)
    (hcoverC : domain origin.cells ⊆ Icc (coarse 0) (coarse (Fin.last (a+1))))
    (hcoverF : domain origin.cells ⊆ Icc (fine 0) (fine (Fin.last (m+1))))
    (hsub : ∀ e, cell (domain origin.cells) fine e ⊆
      cell (domain origin.cells) coarse (pointParents coarse fine e))
    (row : Row) (hpositive : 0 < (μ (active row)).real (domain origin.cells))
    (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ p, (μ (active row)).real (cell (domain origin.cells) coarse p) /
      (μ (active row)).real (domain origin.cells) ≤ eta)
    (jobs : List (Row × Row)) (hbudget : (2 * (jobs.length : ℝ)) * eta < 1) :
    ∃ pairs final, pointRun (physicalCumulative μ active origin) coarse jobs fine = some (pairs,final) ∧
      pairs.length = jobs.length ∧ final.card ≤ 2 * jobs.length := by
  let values := pointValues (physicalCumulative μ active origin) fine
  let weights := fun e => (μ (active row)).real (cell (domain origin.cells) fine e) /
    (μ (active row)).real (domain origin.cells)
  have hnormal : ∑ e, weights e = 1 := by
    rw [show (∑ e, weights e) =
      (∑ e, (μ (active row)).real (cell (domain origin.cells) fine e)) /
        (μ (active row)).real (domain origin.cells) by simp only [weights,Finset.sum_div],
      cell_mass_sum _ _ (domain_measurable _) fine hf hcoverF, div_self hpositive.ne']
  have hparent (p : Fin (a+1)) :
      (∑ e, if pointParents coarse fine e = p then weights e else 0) ≤ eta := by
    have hmass := UpperRecordedParents.fiber_mass_sum (μ (active row))
      (cell (domain origin.cells) fine) (cell (domain origin.cells) coarse)
      (pointParents coarse fine) (cell_measurable _ (domain_measurable _) fine)
      (cells_disjoint _ fine hf)
      (by rw [cells_cover _ fine hf hcoverF,cells_cover _ coarse hc hcoverC])
      (cells_disjoint _ coarse hc) hsub p
    have heq : (∑ e, if pointParents coarse fine e = p then weights e else 0) =
        (∑ e, if pointParents coarse fine e = p then
          (μ (active row)).real (cell (domain origin.cells) fine e) else 0) /
            (μ (active row)).real (domain origin.cells) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp [weights]
    rw [heq,hmass]
    exact hsmall p
  have hnonneg : ∀ r e, 0 ≤ values r e := by
    intro r e
    apply sub_nonneg.mpr
    exact physicalCumulative_monotone μ active origin r
      (hf (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega))
  obtain ⟨pairs, final, hexec, hlen, _, hcard⟩ := table_run_completes weights
    (pointParents coarse fine) eta heta (List.finRange (m+1)) (by simp) hnormal hparent
    values hnonneg jobs ∅ (by simpa only [Finset.card_empty,zero_add,Nat.cast_mul,Nat.cast_ofNat] using hbudget)
  exact ⟨pairs,final,hexec,hlen,by simpa only [Finset.card_empty,zero_add] using hcard⟩

/-- A recorded coarse grid supplies completion on every refining grid,
without obtaining new oracle answers for the inserted test coordinate. -/
theorem recorded_refinement_completes
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : UpperCircularStage.Policy n)
    (hp : UpperCircularStage.Admissible (Chores.measureProfile μ) policy)
    (active : Row → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q : ℕ)
    (fine : Fin (m+2) → ℝ) (hf : Monotone fine) (hf0 : fine 0 = 0)
    (hf1 : fine (Fin.last (m+1)) = 1)
    (hcontains : ∀ c, ∃ f, fine f = UpperRecordedQuantiles.cuts policy active origin q c)
    (jobs : List (Row × Row)) (hbudget : 2 * jobs.length < q+1) :
    ∃ pairs final, pointRun (physicalCumulative μ active origin)
      (UpperRecordedQuantiles.cuts policy active origin q) jobs fine = some (pairs,final) ∧
      pairs.length = jobs.length ∧ final.card ≤ 2 * jobs.length := by
  let coarse := UpperRecordedQuantiles.cuts policy active origin q
  have hc : Monotone coarse := UpperCommonGrid.grid_monotone _
  have hend := UpperRecordedQuantiles.cuts_endpoints μ policy hp active origin hgood hpositive q
  have hzero := UpperGridInterior.coarse_zero_only μ policy hp active origin hgood hpositive q
  have hsub : ∀ e, cell (domain origin.cells) fine e ⊆
      cell (domain origin.cells) coarse (pointParents coarse fine e) := by
    intro e
    have hfit := UpperGridParents.parent_fits coarse fine hc hf hend.1 hf0 hend.2 hf1 hzero hcontains e
    have hparent := parent_interval coarse fine hc hend.1 hf0 hzero e
    rw [hparent] at hfit
    exact UpperGridParents.cell_subset_parent _ coarse fine hend.1 hf0 e _ hfit
  let row : Row := Classical.choice inferInstance
  apply physical_pointRun_completes μ active origin coarse hc fine hf
    (by dsimp [coarse]; rw [hend.1,hend.2]; exact domain_subset_unit _)
    (by rw [hf0,hf1]; exact domain_subset_unit _) hsub row (hpositive row)
    (1/(q+1 : ℝ)) (by positivity)
    (UpperRecordedQuantiles.logical_cells_small μ policy hp active origin hgood hpositive q row) jobs
  rw [mul_one_div]
  apply (div_lt_one (by positivity : (0 : ℝ) < q+1)).mpr
  exact_mod_cast hbudget

end EnvyFreeResearch.Full.RefinedUpperPeeling
