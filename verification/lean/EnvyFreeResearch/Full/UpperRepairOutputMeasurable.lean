import EnvyFreeResearch.Full.UpperRepair

/-! Joint Borel physical Repair outputs, including rejection and restored
material, for changing input caches and the full original private tape. -/

noncomputable section
open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairOutputMeasurable

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram UpperLogicalIsolation
  UpperCorrectionStageProgram

variable {n k q m L : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem afterGrid_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → Grid n k q m)
    (L : ℕ) (theta : I) (cap eta lam : ℝ) (p : X → Tape k q m L)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hdata : Measurable data) (hp : Measurable p) :
    Measurable (fun x => afterGrid policy active (origin x) (data x) theta (p x).1 eta lam
      (fun d => dataTargets hk q chores active (origin x) (old x) d L theta (p x).1 (p x).2.1.2.1 (p x).2.1.2.2 lam)
      (fun d => approved hk chores active (origin x) (old x) d L theta cap lam (p x).1 (p x).2.1.2.1 (p x).2.1.2.2)
      (p x).2.2) := by
  have hlabels := measurable_fst.comp hp
  have hisolation := measurable_snd.comp (measurable_fst.comp (measurable_snd.comp hp))
  have hpi := measurable_fst.comp hisolation
  have hthreshold := measurable_snd.comp hisolation
  have hstarts := measurable_snd.comp (measurable_snd.comp hp)
  have ht := dataTargets_measurable hk q chores active origin old data L theta
    (fun x => (p x).1) (fun x => (p x).2.1.2.1) (fun x => (p x).2.1.2.2) lam
    horigin hold hdata (fun c => (measurable_pi_apply c).comp hlabels) hpi
    (fun j => (measurable_pi_apply j).comp hthreshold)
  have ha := approved_measurable hk chores active origin old data L theta cap lam
    (fun x => (p x).1) (fun x => (p x).2.1.2.1) (fun x => (p x).2.1.2.2)
    horigin hold hdata (fun c => (measurable_pi_apply c).comp hlabels) hpi
    (fun j => (measurable_pi_apply j).comp hthreshold)
  have hstage := executeStage_measurable policy hmeas active
    (fun x => UpperGridData.reserve (data x) theta (p x).1) (fun x => UpperGridData.cuts (data x))
    (fun x => dataTargets hk q chores active (origin x) (old x) (data x) L theta (p x).1 (p x).2.1.2.1 (p x).2.1.2.2 lam)
    (fun _ => eta) (fun _ => lam) (fun x => (p x).2.2)
    (UpperGridData.reserve_measurable data theta _ hdata (fun c => (measurable_pi_apply c).comp hlabels))
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable data hdata)) ht measurable_const measurable_const
    (fun j => (measurable_pi_apply j).comp hstarts)
  have hrestore : Measurable (fun x => (⟨(origin x).cells, (data x).2.2.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (data x).2.2.history))
    exact (state_cells_measurable.comp horigin).prodMk
      (state_history_measurable.comp (measurable_snd.comp (measurable_snd.comp hdata)))
  exact (hdata.prodMk (UpperPreparedTrialProgramMeasurable.rollback_measurable origin _ horigin hstage)).ite
    (measurableSet_eq_fun ha (measurable_const (a := true)))
    (hdata.prodMk (measurable_const.prodMk (hrestore.prodMk measurable_const)))

theorem trial_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ)
    (theta : I) (cap eta lam : ℝ) (p : X → Tape k q m L)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Measurable (fun x => UpperRepairTrialFull.result policy hk chores active (origin x) (old x)
      q m L theta cap eta lam (p x)) := by
  have hdraw := measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hp))
  have hd := (UpperGridMerge.prepare_measurable policy hmeas active q m).comp (horigin.prodMk hdraw)
  have hb := afterGrid_measurable policy hmeas hk chores active origin old
    (fun x => UpperGridMerge.prepare policy active (origin x) q m (p x).2.1.1)
    L theta cap eta lam p horigin hold hd hp
  exact UpperRepairTrialFull.finish_measurable active origin theta (fun x => (p x).1)
    (fun x => UpperRepairTrialRejection.result policy hk chores active (origin x) (old x) q m L theta cap eta lam (p x))
    horigin (fun c => (measurable_pi_apply c).comp (measurable_fst.comp hp)) hb

theorem execute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ)
    (theta : I) (cap eta lam : ℝ) (p : X → Tape k q m L)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Measurable (fun x => UpperRepairProgram.execute policy hk chores active (origin x) (old x)
      q m L theta cap eta lam (p x)) := by
  have hr := trial_measurable policy hmeas hk chores active origin old q m L theta cap eta lam p horigin hold hp
  have hi := measurable_snd.comp (measurable_fst.comp (measurable_snd.comp hp))
  exact UpperRepairProgram.finish_measurable hk chores active origin old L theta
    (fun x => (p x).1) (fun x => (p x).2.1.2.1) (fun x => (p x).2.1.2.2)
    (fun x => UpperRepairTrialFull.result policy hk chores active (origin x) (old x) q m L theta cap eta lam (p x))
    horigin hold (fun c => (measurable_pi_apply c).comp (measurable_fst.comp hp))
    (measurable_fst.comp hi) (fun j => (measurable_pi_apply j).comp (measurable_snd.comp hi)) hr

end EnvyFreeResearch.Full.UpperRepairOutputMeasurable
