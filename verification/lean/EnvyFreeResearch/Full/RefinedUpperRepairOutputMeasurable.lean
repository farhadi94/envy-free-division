import EnvyFreeResearch.Full.RefinedUpperRepairLaw

/-! Joint Borel physical outputs for arbitrary changing recorded inputs and
the complete original random tape, including rejected attempts. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairOutputMeasurable
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperCorrectionLoop RefinedUpperCorrectionSetup RefinedUpperPreparationProgram RefinedUpperRepairTargets
variable {n k coarse fine m L r : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem after_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (chores : Bool) (active : Fin k → Fin n) (origin : X → State n)
    (p : X → Prepared n k coarse fine) (eta lam : ℝ)
    (tape : X → Fin k → Fin r → UpperCircular.Circle)
    (ho : Measurable origin) (hp : Measurable p) (htape : ∀ j, Measurable (fun x => tape x j)) :
    Measurable (fun x => RefinedUpperRepairTrial.after policy chores active (origin x) (p x) eta lam (tape x)) := by
  have hres := measurable_fst.comp (measurable_snd.comp hp)
  have hcuts (e) := (measurable_pi_apply e).comp (UpperGridData.cuts_measurable _ (measurable_fst.comp hp))
  have ht := targets_measurable chores active p eta lam hp
  have hj := tasks_measurable active _ _ _ (fun _ => eta) (fun _ => lam) hres hcuts ht measurable_const measurable_const
  have hs := startState_measurable active _ _ _ (fun _ => eta) hres hcuts ht measurable_const
  have hb := RefinedUpperCorrectionOutputMeasurable.run_measurable policy hmeas _ _ tape
    (fun j => (measurable_pi_apply j).comp hj) hs htape
  exact (hp.prodMk (measurable_snd.comp hb)).ite
    (measurableSet_eq_fun (approved_measurable chores active p lam hp) measurable_const)
    (hp.prodMk (RefinedUpperRepairTrial.rejected_measurable origin p ho hp))

theorem execute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q : ℕ) (eta lam : ℝ)
    (p : X → RefinedUpperRepairLaw.Tape k m L r)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Measurable (fun x => RefinedUpperRepairLaw.execute policy hk chores active (origin x) (old x) q eta lam (p x)) := by
  have hparam := measurable_fst.comp hp
  have hdraw := measurable_fst.comp hparam
  have hi := measurable_snd.comp hparam
  have hpi := measurable_fst.comp hi
  have hthreshold := measurable_snd.comp hi
  have hgrid := (UpperGridMerge.prepare_measurable policy hmeas active q m).comp (ho.prodMk hdraw)
  have hprep := finish_measurable hk chores active origin old _ L
    (fun x => (p x).1.2.1) (fun x => (p x).1.2.2) ho hold hgrid hpi
    (fun j => (measurable_pi_apply j).comp hthreshold)
  have htrial := after_measurable policy hmeas chores active origin _ eta lam (fun x => (p x).2) ho hprep
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp hp))
  exact RefinedUpperRepairProgram.finish_measurable hk chores active origin old L
    (fun x => (p x).1.2.1) (fun x => (p x).1.2.2) eta lam _ ho hold hpi
    (fun j => (measurable_pi_apply j).comp hthreshold) htrial

end EnvyFreeResearch.Full.RefinedUpperRepairOutputMeasurable
