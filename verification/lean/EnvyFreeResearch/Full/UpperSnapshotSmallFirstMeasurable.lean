import EnvyFreeResearch.Full.UpperSnapshotSmallFirstExecution

/-! Joint Borel first-stage computation from the complete cached state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m : ℕ} {X : Type*} [MeasurableSpace X]
variable (origin : X → State n) (cutter : Fin n) (cuts : X → Fin (m + 2) → ℝ)
  (selected : X → Finset (Fin (m + 1))) (t : X → ℝ)
  (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
  (hselected : Measurable selected) (ht : Measurable t)
include horigin hcuts hselected ht

theorem firstFill_measurable : Measurable (fun x => firstFill (origin x) cutter (cuts x) (selected x) (t x)) :=
  decide_measurable _ (measurableSet_lt
    (total_measurable _ (fun _ => cutter) (retain_measurable origin cuts selected horigin hcuts hselected) measurable_const)
    (ht.mul (total_measurable origin (fun _ => cutter) horigin measurable_const)))

theorem firstSource_measurable : Measurable (fun x => firstSource (origin x) cutter (cuts x) (selected x) (t x)) := by
  have hp := UpperPendingExclusion.selected_measurable cuts (fun x (_ : Unit) => selected x)
    hcuts (fun _ => hselected)
  have hn := selectState_measurable origin (fun x c => !positiveFlag (cuts x) (selected x) c) horigin
    ((measurable_of_countable (fun b : Bool => !b)).comp hp)
  exact hn.ite (measurableSet_eq_fun (firstFill_measurable origin cutter cuts selected t horigin hcuts hselected ht)
    measurable_const) (retain_measurable origin cuts selected horigin hcuts hselected)

theorem firstDeficit_measurable : Measurable (fun x => firstDeficit (origin x) cutter (cuts x) (selected x) (t x)) := by
  have htotal := ht.mul (total_measurable origin (fun _ => cutter) horigin measurable_const)
  exact (htotal.sub (total_measurable _ (fun _ => cutter)
    (retain_measurable origin cuts selected horigin hcuts hselected) measurable_const)).ite
    (measurableSet_eq_fun (firstFill_measurable origin cutter cuts selected t horigin hcuts hselected ht) measurable_const)
    htotal

theorem firstAmount_measurable : Measurable (fun x => firstAmount (origin x) cutter (cuts x) (selected x) (t x)) :=
  amount_measurable _ _ (firstDeficit_measurable origin cutter cuts selected t horigin hcuts hselected ht)
    (total_measurable _ (fun _ => cutter)
      (firstSource_measurable origin cutter cuts selected t horigin hcuts hselected ht) measurable_const)

variable (policy : Policy n) (hmeas : MeasurablePolicy policy) (start : X → Circle) (hstart : Measurable start)
include hmeas hstart

theorem firstRun_measurable :
    Measurable (fun x => firstRun policy (origin x) cutter (cuts x) (selected x) (t x) (start x)) := by
  apply partitionRun_measurable policy hmeas _ cutter _ start
    (firstSource_measurable origin cutter cuts selected t horigin hcuts hselected ht) _ hstart
  intro j
  fin_cases j
  · exact measurable_const
  · exact firstAmount_measurable origin cutter cuts selected t horigin hcuts hselected ht
  · exact measurable_const

theorem firstRestored_measurable :
    Measurable (fun x => firstRestored policy (origin x) cutter (cuts x) (selected x) (t x) (start x)) := by
  have hr := firstRun_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart
  apply measurable_comap_iff.mpr
  change Measurable (fun x => (refineEndpoints (origin x).cells
    (List.ofFn (firstRun policy (origin x) cutter (cuts x) (selected x) (t x) (start x)).1),
    (firstRun policy (origin x) cutter (cuts x) (selected x) (t x) (start x)).2.history))
  exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp horigin)
    ((UpperRecordedGrid.ofFn_measurable 2).comp (measurable_fst.comp hr))).prodMk
    (state_history_measurable.comp (measurable_snd.comp hr))

theorem firstFlag_measurable :
    Measurable (fun p : X × Component => firstFlag policy (origin p.1) cutter (cuts p.1)
      (selected p.1) (t p.1) (start p.1) p.2) := by
  have hr := firstRun_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart
  have hp := UpperPendingExclusion.selected_measurable cuts (fun x (_ : Unit) => selected x)
    hcuts (fun _ => hselected)
  have ha := prefixAtom_measurable _ _ _ _ _
    ((firstAmount_measurable origin cutter cuts selected t horigin hcuts hselected ht).comp measurable_fst)
    (hstart.comp measurable_fst)
    (((measurable_pi_apply 0).comp (measurable_fst.comp hr)).comp measurable_fst)
    (((measurable_pi_apply 1).comp (measurable_fst.comp hr)).comp measurable_fst) measurable_snd
  exact ((measurable_of_countable (fun p : Bool × Bool => p.1 || p.2)).comp (hp.prodMk ha)).ite
    (measurableSet_eq_fun ((firstFill_measurable origin cutter cuts selected t horigin hcuts hselected ht).comp
      measurable_fst) measurable_const)
    ((measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp (hp.prodMk ha))

theorem firstEndowment_measurable :
    Measurable (fun x => firstEndowment policy (origin x) cutter (cuts x) (selected x) (t x) (start x)) :=
  selectState_measurable _ _
    (firstRestored_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart)
    (firstFlag_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart)

theorem firstRemainder_measurable :
    Measurable (fun x => firstRemainder policy (origin x) cutter (cuts x) (selected x) (t x) (start x)) :=
  selectState_measurable _ _
    (firstRestored_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart)
    ((measurable_of_countable (fun b : Bool => !b)).comp
      (firstFlag_measurable origin cutter cuts selected t horigin hcuts hselected ht policy hmeas start hstart))

end EnvyFreeResearch.Full.UpperSnapshotSmall
