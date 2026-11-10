import EnvyFreeResearch.Full.RefinedUpperStabilityFreshPoint
import EnvyFreeResearch.Full.RefinedUpperStabilityCellGap

/-! The deletion certificate controls the physical interpolation error on
the retained buffer, using the actual retained-table cell gap. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperStability
open RefinedUpperPeeling RefinedUpperPreparation UpperRecordedDomain UpperCorrectionExecution
  UpperGridInterpolation UpperSortedGrid UpperDomainDifference
variable {n k a b m : ℕ} [Nonempty (Fin k)]

theorem retained_point_control
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (origin reserve : State n)
    (hreserve : WellFormed μ reserve)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (coarse : Fin (a+2) → ℝ) (hc : Monotone coarse) (hc0 : coarse 0 = 0)
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ)
    (hf0 : sorted (augmented permanent samples) 0 = 0)
    (hsep : ∀ e, SeparatedAt (sorted (augmented permanent samples) e) reserve.cells)
    (jobs finalJobs : List (Fin k × Fin k))
    (pairs : List (Fin (b+m+2) × Fin (b+m+2)))
    (pairs' : List (Fin (b+m+1) × Fin (b+m+1)))
    (final final' : Finset (Fin (a+1))) (z : ℝ)
    (hz : 0 < z ∧ z < 1) (hnew : ∀ e, augmented permanent samples e ≠ z)
    (hexec : pointRun (physicalCumulative μ active origin) coarse jobs
      (sorted (augmented permanent (Fin.cons z samples))) = some (pairs,final))
    (hexec' : pointRun (physicalCumulative μ active origin) coarse jobs
      (sorted (augmented permanent samples)) = some (pairs',final'))
    (hfit : ∀ e : Fin (b+m+1), intervalFits coarse
      (intervalLabel (sorted (augmented permanent samples)) e)
      (intervalParent coarse (intervalLabel (sorted (augmented permanent samples)) e)))
    (hT : domain reserve.cells = ⋃ p, if p ∉ final' then
      UpperLogicalCells.cell (domain origin.cells) coarse p else ∅)
    (ht : z ∈ domain reserve.cells)
    (hbad : z ∉ protectedBad (endpointProcedure (physicalCumulative μ active origin)
      coarse jobs finalJobs) permanent samples)
    (i j : Fin k) (hij : (i,j) ∈ finalJobs) :
    physicalError (fun r => μ (active r))
      (fun r => (μ (active r)).real (domain reserve.cells)) reserve.cells
      (sorted (augmented permanent samples)) z i j ≤
      2 * UpperPayments.cellGap
        (RefinedUpperCorrectionSetup.table active reserve (sorted (augmented permanent samples))) i j := by
  let fine := sorted (augmented permanent samples)
  let gap := UpperPayments.cellGap (RefinedUpperCorrectionSetup.table active reserve fine) i j
  have hsurvive : ∀ e : Fin (b+m+1), fine e.castSucc < z → z < fine e.succ →
      intervalParent coarse (intervalLabel fine e) ∉ final' := by
    intro e hl hr
    apply retained_union_parent_survives (domain origin.cells) coarse hc final'
      (fine e.castSucc) z (fine e.succ) hl hr (hfit e)
    · simpa only [← hT] using ht
    · rw [hc0]
      exact hz.1.ne'
  have hA : ∀ c ∈ List.ofFn (intervalLabel fine), intervalParent coarse c ∉ final' →
      |((μ (active i)).real (domain origin.cells)/(μ (active i)).real (domain reserve.cells)) *
          intervalValues (physicalCumulative μ active origin) i c -
        ((μ (active j)).real (domain origin.cells)/(μ (active j)).real (domain reserve.cells)) *
          intervalValues (physicalCumulative μ active origin) j c| ≤ gap := by
    intro c hmem hparent
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hmem
    exact retained_cell_gap μ active origin reserve hreserve hpositive coarse final' hT fine
      hf0 (sorted_monotone _) hsep e _ (hfit e) hparent i j
  obtain ⟨e,hl,hr,hprefix,hsuffix⟩ := fresh_point_control
    (physicalCumulative μ active origin) (physicalCumulative_monotone μ active origin)
    coarse hc permanent samples z hz hnew jobs finalJobs pairs pairs' final final'
    hexec hexec' hfit hsurvive hbad i j hij
    ((μ (active i)).real (domain origin.cells)/(μ (active i)).real (domain reserve.cells))
    ((μ (active j)).real (domain origin.cells)/(μ (active j)).real (domain reserve.cells)) gap hA
  exact retained_physicalError_le μ active origin reserve.cells
    (fun r => (μ (active r)).real (domain reserve.cells)) hpositive coarse final' hT fine
    (sorted_monotone _) hf0 e _ (hfit e) (hsurvive e hl hr) z hl.le hr.le i j gap hprefix hsuffix

end EnvyFreeResearch.Full.RefinedUpperStability
