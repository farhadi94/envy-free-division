import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestoredMeasurable

/-! Second-stage Borel execution with a varying share target. The policy
receives the full realized first-stage history at every second-stage query. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]

theorem remainderTargets_joint_measurable (t : X → ℝ) (ht : Measurable t) (j : Fin (J+1)) :
    Measurable (fun x => remainderTargets J (t x) j) := by
  unfold remainderTargets
  split_ifs
  · exact amount_measurable _ _ (measurable_const.mul ht) (measurable_const.sub ht)
  · exact measurable_const

variable (policy : Policy n) (hmeas : MeasurablePolicy policy)
  (origin : X → State n) (cutter : Fin n) (cuts : X → Fin (m+2) → ℝ)
  (selected : X → Finset (Fin (m+1))) (t : X → ℝ) (first second : X → Circle)
  (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
  (hselected : Measurable selected) (ht : Measurable t)
  (hfirst : Measurable first) (hsecond : Measurable second)
include hmeas horigin hcuts hselected ht hfirst hsecond

theorem secondRun_joint_measurable :
    Measurable (fun x => secondRun (J:=J) policy (origin x) cutter (cuts x) (selected x)
      (t x) (first x) (second x)) := by
  exact partitionRun_measurable policy hmeas _ cutter (fun x => remainderTargets J (t x)) second
    (firstRemainder_measurable origin cutter cuts selected t horigin hcuts hselected ht
      policy hmeas first hfirst) (remainderTargets_joint_measurable t ht) hsecond

theorem secondPiece_joint_measurable (hJ : 0 < J) (j : Fin J) :
    Measurable (fun x => secondPiece hJ policy (origin x) cutter (cuts x) (selected x)
      (t x) (first x) (second x) j) := by
  exact partState_measurable hJ policy hmeas _ cutter (fun x => remainderTargets J (t x)) second
    (firstRemainder_measurable origin cutter cuts selected t horigin hcuts hselected ht
      policy hmeas first hfirst) (remainderTargets_joint_measurable t ht) hsecond j

theorem secondRestored_joint_measurable :
    Measurable (fun x => secondRestored (J:=J) policy (origin x) cutter (cuts x) (selected x)
      (t x) (first x) (second x)) := by
  have hs := firstRestored_measurable origin cutter cuts selected t horigin hcuts hselected
    ht policy hmeas first hfirst
  have hr := secondRun_joint_measurable (J:=J) policy hmeas origin cutter cuts selected t first second
    horigin hcuts hselected ht hfirst hsecond
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    (refineEndpoints (firstRestored policy (origin x) cutter (cuts x) (selected x) (t x) (first x)).cells
      (List.ofFn (secondRun (J:=J) policy (origin x) cutter (cuts x) (selected x) (t x) (first x) (second x)).1),
     (secondRun (J:=J) policy (origin x) cutter (cuts x) (selected x) (t x) (first x) (second x)).2.history))
  exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp hs)
    ((UpperRecordedGrid.ofFn_measurable J).comp (measurable_fst.comp hr))).prodMk
    (state_history_measurable.comp (measurable_snd.comp hr))
end EnvyFreeResearch.Full.UpperSnapshotSmall
