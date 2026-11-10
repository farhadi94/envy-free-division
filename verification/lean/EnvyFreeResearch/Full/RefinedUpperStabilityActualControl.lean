import EnvyFreeResearch.Full.RefinedUpperStabilityRetainedControl
import EnvyFreeResearch.Full.RefinedUpperStabilityAugmentedSupply
import EnvyFreeResearch.Full.RefinedUpperPreparationExecution
import EnvyFreeResearch.Full.RefinedUpperEndpointExceptions

/-! Pointwise control for the actual sampled preparation. All peeling runs,
parent fits, retained-domain identities, and cache facts are derived from the
ordinary query execution; the only exception is its explicit analytic bad set. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperStability
open RefinedUpperPeeling RefinedUpperPreparation UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperGridInterpolation UpperSortedGrid UpperDomainDifference
variable {n k : ℕ} [Nonempty (Fin k)]

theorem actual_point_control
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(UpperRepairJobs.jobCount k*L) < q+1)
    (finalJobs : List (Fin k × Fin k)) (z : ℝ)
    (hout : z ∉ RefinedUpperEndpointExceptions.augment
      (physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L) finalJobs
        (UpperGridMerge.prepare policy active origin q m draw).1
        (UpperGridMerge.prepare policy active origin q m draw).2.1)
      (domain (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L).cells)
      (UpperGridMerge.cuts policy active origin q m draw))
    (i j : Fin k) (hij : (i,j) ∈ finalJobs) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let reserve := dataRetained active origin data L
    physicalError (fun r => μ (active r))
      (fun r => (μ (active r)).real (domain reserve.cells)) reserve.cells
      (UpperGridData.cuts data) z i j ≤ 2 * dataDisagreement active origin data L i j := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let fine := UpperGridMerge.cuts policy active origin q m draw
  let coarse := UpperRecordedQuantiles.cuts policy active origin q
  let reserve := dataRetained active origin data L
  let result := dataResult active origin data L
  let jobs := UpperLogicalIsolation.requests k L
  have hf : fine = sorted (augmented data.1 data.2.1) := UpperGridData.cuts_eq_augmented data
  have hends := UpperGridMerge.cuts_endpoints μ policy hp active origin hgood hpositive q m draw
  obtain ⟨hbad,ht,hgrid⟩ := RefinedUpperEndpointExceptions.outside_augment _ _ _ z hout
  have hzunit : z ∈ Icc (0 : ℝ) 1 := domain_subset_unit reserve.cells ht
  have hz0 : z ≠ 0 := by
    intro he
    apply hgrid
    exact ⟨0,hends.1.trans he.symm⟩
  have hz1 : z ≠ 1 := by
    intro he
    apply hgrid
    exact ⟨Fin.last _,hends.2.trans he.symm⟩
  have hz : 0 < z ∧ z < 1 := ⟨lt_of_le_of_ne hzunit.1 hz0.symm,lt_of_le_of_ne hzunit.2 hz1⟩
  have hnew : ∀ e, augmented data.1 data.2.1 e ≠ z := by
    intro e he
    apply hgrid
    refine ⟨(UpperSortedGrid.select (augmented data.1 data.2.1)).symm e,?_⟩
    change fine _ = z
    rw [hf]
    change (augmented data.1 data.2.1)
      (UpperSortedGrid.select (augmented data.1 data.2.1)
        ((UpperSortedGrid.select (augmented data.1 data.2.1)).symm e)) = z
    rw [Equiv.apply_symm_apply]
    exact he
  have hrecorded : pointRun (physicalCumulative μ active origin) coarse jobs fine = some result := by
    rw [pointRun_recorded μ policy hp active origin hgood hpositive]
    exact (dataResult_spec μ policy hp active origin hgood hpositive q m L draw hbudget).1
  have hjobs : 2*jobs.length < q+1 := by
    simpa only [jobs,UpperLogicalIsolation.requests_length] using hbudget
  obtain ⟨pairs,final,hexec,_,_⟩ := inserted_recorded_run_completes μ policy hp active origin
    hgood hpositive q m draw z hzunit jobs hjobs
  have hfit : ∀ e, intervalFits coarse (intervalLabel fine e)
      (intervalParent coarse (intervalLabel fine e)) := by
    intro e
    have h := UpperRecordedParents.parent_fits μ policy hp active origin hgood hpositive q m draw e
    rw [recorded_parent_interval μ policy hp active origin hgood hpositive] at h
    exact ⟨h.1,h.2.1⟩
  have hT : domain reserve.cells = ⋃ p, if p ∉ result.2 then
      UpperLogicalCells.cell (domain origin.cells) coarse p else ∅ :=
    retainedState_domain μ policy hp active origin hgood hpositive q m draw result.2
  have hsep : ∀ e, SeparatedAt (fine e) reserve.cells :=
    UpperLogicalPreparation.reserveState_separated policy active origin q m draw 0
      (retentionLabels result.2)
  have hwf : WellFormed μ reserve :=
    retainedState_wellFormed μ policy hp active origin hgood hpositive q m draw result.2
  have hbound := retained_point_control μ active origin reserve hwf hpositive coarse
    (UpperCommonGrid.grid_monotone _) (UpperRecordedQuantiles.cuts_endpoints μ policy hp
      active origin hgood hpositive q).1 data.1 data.2.1
    (by simpa only [← hf] using hends.1)
    (by simpa only [← hf] using hsep) jobs finalJobs pairs result.1 final result.2 z hz hnew
    hexec (by simpa only [← hf] using hrecorded)
    (by simpa only [← hf] using hfit) hT ht hbad i j hij
  have htables : RefinedUpperCorrectionSetup.table active reserve fine =
      UpperCorrectionSetup.table active reserve fine := by
    funext r e
    rfl
  rw [← hf,htables] at hbound
  exact hbound

end EnvyFreeResearch.Full.RefinedUpperStability
