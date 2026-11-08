import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestored
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondMeasurable

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]
variable (policy : Policy n) (hmeas : MeasurablePolicy policy)
  (origin : X → State n) (cutter : Fin n) (cuts : X → Fin (m + 2) → ℝ)
  (selected : X → Finset (Fin (m + 1))) (t : ℝ) (first second : X → Circle)
  (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
  (hselected : Measurable selected) (hfirst : Measurable first) (hsecond : Measurable second)
include hmeas horigin hcuts hselected hfirst hsecond

theorem secondRun_measurable :
    Measurable (fun x => secondRun (J := J) policy (origin x) cutter (cuts x) (selected x) t (first x) (second x)) := by
  exact partitionRun_measurable policy hmeas _ cutter (fun _ => remainderTargets J t) second
    (firstRemainder_measurable origin cutter cuts selected (fun _ => t) horigin hcuts hselected
      measurable_const policy hmeas first hfirst) (fun _ => measurable_const) hsecond

theorem secondRestored_measurable :
    Measurable (fun x => secondRestored (J := J) policy (origin x) cutter (cuts x) (selected x) t (first x) (second x)) := by
  have hs := firstRestored_measurable origin cutter cuts selected (fun _ => t) horigin hcuts hselected
    measurable_const policy hmeas first hfirst
  have hr := secondRun_measurable (J := J) policy hmeas origin cutter cuts selected t first second
    horigin hcuts hselected hfirst hsecond
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    (refineEndpoints (firstRestored policy (origin x) cutter (cuts x) (selected x) t (first x)).cells
      (List.ofFn (secondRun (J := J) policy (origin x) cutter (cuts x) (selected x) t (first x) (second x)).1),
     (secondRun (J := J) policy (origin x) cutter (cuts x) (selected x) t (first x) (second x)).2.history))
  exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp hs)
    ((UpperRecordedGrid.ofFn_measurable J).comp (measurable_fst.comp hr))).prodMk
    (state_history_measurable.comp (measurable_snd.comp hr))

end EnvyFreeResearch.Full.UpperSnapshotSmall
