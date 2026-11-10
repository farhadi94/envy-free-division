import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeMeasurableCore
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeProgram
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMachineMeasurable

/-! Borel physical normalization output under a jointly measurable ordinary
query policy. No measurability premise about the desired output is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open MeasureTheory RefinedUpperGlobalPhysical UpperCorrectionExecution UpperBaseCases
open UpperCircularStage UpperStageMeasurable
variable {n : ℕ}

theorem twoAgentTerminal_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (chores : Bool) (cutter chooser : Fin n) :
    Measurable (fun a : Anchor n => twoAgentTerminal policy chores a cutter chooser) := by
  have hhalf : Measurable (fun a : Anchor n => halfRun policy a.residue cutter) := by
    change Measurable (fun a : Anchor n => UpperRecordedGrid.execute policy
      (fun (_ : Unit) => cutter) a.residue 1 (fun _ => ((),half)))
    have hr := UpperRecordedGrid.execute_measurable policy hpolicy (fun (_ : Unit) => cutter) 1
    have hi : Measurable (fun a : Anchor n => (a.residue,fun (_ : Fin 1) => ((),half))) :=
      anchor_residue_measurable.prodMk measurable_const
    have hh := hr.comp hi
    convert hh using 1
    funext a
    rfl
  exact terminal_measurable id measurable_id _ (finish_measurable chores cutter chooser _ hhalf)
    _ (state_history_measurable.comp (measurable_snd.comp hhalf))

theorem requestExecute_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (chores : Bool) : Measurable (requestExecute policy chores) := by
  have ht : Measurable (fun p : Anchor n × Fin n × Fin n =>
      Phase.done (twoAgentTerminal policy chores p.1 p.2.1 p.2.2)) := by
    apply phase_done_measurable.comp
    refine finite_select_measurable (fun p : Anchor n × Fin n × Fin n => p.2.1)
      (measurable_fst.comp measurable_snd)
      (fun cutter p => twoAgentTerminal policy chores p.1 cutter p.2.2) ?_
    intro cutter
    refine finite_select_measurable (fun p : Anchor n × Fin n × Fin n => p.2.2)
      (measurable_snd.comp measurable_snd)
      (fun chooser p => twoAgentTerminal policy chores p.1 cutter chooser) ?_
    intro chooser
    exact (twoAgentTerminal_measurable policy hpolicy chores cutter chooser).comp measurable_fst
  have h : Measurable (fun c : Anchor n ⊕ ((Anchor n × Fin n × Fin n) ⊕ Anchor n) =>
      c.elim Phase.done (Sum.elim
        (fun p => Phase.done (twoAgentTerminal policy chores p.1 p.2.1 p.2.2)) Phase.snapshot)) :=
    phase_done_measurable.sumElim (ht.sumElim phase_snapshot_measurable)
  convert h.comp (comap_measurable Request.code) using 1
  funext request
  cases request <;> rfl

theorem execute_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) : Measurable (execute policy fallback chores) :=
  (requestExecute_measurable policy hpolicy chores).comp (normalize_measurable fallback chores n)

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
