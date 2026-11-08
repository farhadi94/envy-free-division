import EnvyFreeResearch.Full.UpperSnapshotSmallRecorded

/-! Joint Borel construction of the recorded shared-circle pieces. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable Chores
variable {n J : ℕ} {X : Type*} [MeasurableSpace X]

theorem selectState_measurable (state : X → State n) (keep : X → Component → Bool)
    (hstate : Measurable state) (hkeep : Measurable (fun p : X × Component => keep p.1 p.2)) :
    Measurable (fun x => selectState (state x) (keep x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => ((state x).cells.filter (keep x), (state x).history))
  exact (list_filter_measurable keep _ hkeep (state_cells_measurable.comp hstate)).prodMk
    (state_history_measurable.comp hstate)

theorem prefixAtom_measurable (amount : X → I) (start : X → Circle)
    (first last : X → ℝ) (cell : X → Component)
    (ha : Measurable amount) (hs : Measurable start) (hf : Measurable first)
    (hl : Measurable last) (hc : Measurable cell) :
    Measurable (fun x => prefixAtom (amount x) (start x) (first x) (last x) (cell x)) := by
  have hr := component_right_measurable.comp hc
  have hinside := decide_measurable (fun x => first x < (cell x).right ∧ (cell x).right ≤ last x)
    ((measurableSet_lt hf hr).inter (measurableSet_le hr hl))
  have houtside := decide_measurable (fun x => ¬(last x < (cell x).right ∧ (cell x).right ≤ first x))
    (((measurableSet_lt hl hr).inter (measurableSet_le hr hf)).compl)
  have hw : MeasurableSet {x | value (start x) < value (start x + project (amount x))} :=
    measurableSet_lt (measurable_value.comp hs)
      (measurable_value.comp (hs.add (measurable_project.comp ha)))
  exact measurable_const.ite (measurableSet_eq_fun ha measurable_const)
    (measurable_const.ite (measurableSet_eq_fun ha measurable_const) (hinside.ite hw houtside))

theorem partState_measurable (hJ : 0 < J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (origin : X → State n) (cutter : Fin n) (q : X → Fin (J + 1) → I) (start : X → Circle)
    (horigin : Measurable origin) (hq : ∀ j, Measurable (fun x => q x j)) (hstart : Measurable start)
    (j : Fin J) : Measurable (fun x => partState hJ policy (origin x) cutter (q x) (start x) j) := by
  let result (x : X) := partitionRun policy (origin x) cutter (q x) (start x)
  have hr : Measurable result := partitionRun_measurable policy hmeas origin cutter q start horigin hq hstart
  have hp (i : Fin J) : Measurable (fun x => (result x).1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp hr)
  have hb (i : Fin (J + 1)) : Measurable (fun x => boundary hJ (result x).1 i) :=
    boundary_measurable hJ _ hp i
  have ha (i : Fin (J + 1)) : Measurable (fun p : X × Component =>
      prefixAtom (q p.1 i) (start p.1) ((result p.1).1 ⟨0, hJ⟩)
        (boundary hJ (result p.1).1 i) p.2) :=
    prefixAtom_measurable _ _ _ _ _ ((hq i).comp measurable_fst) (hstart.comp measurable_fst)
      ((hp _).comp measurable_fst) ((hb i).comp measurable_fst) measurable_snd
  exact selectState_measurable _ _ (measurable_snd.comp hr)
    ((measurable_of_countable (fun p : Bool × Bool => p.1 && !p.2)).comp
      ((ha j.succ).prodMk (ha j.castSucc)))

end EnvyFreeResearch.Full.UpperSnapshotSmall
