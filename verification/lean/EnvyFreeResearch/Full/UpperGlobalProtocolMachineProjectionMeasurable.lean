import EnvyFreeResearch.Full.UpperGlobalProtocolMachineMeasurable
import EnvyFreeResearch.Full.UpperGlobalProtocolDispatch

/-! Borel projections of the actual tagged global phase. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCorrectionExecution
variable {n : ℕ}

theorem phase_code_measurable : Measurable (Phase.code (n:=n)) := comap_measurable _

theorem phase_anchor_measurable : Measurable (Phase.anchor (n:=n)) := by
  let f : (Fin 3 × Anchor n) ⊕ (Fin 3 × Pending n × ℝ) → Anchor n :=
    Sum.elim Prod.snd (fun x => x.2.1.anchor)
  have hf : Measurable f := measurable_snd.sumElim
    (pending_anchor_measurable.comp (measurable_fst.comp measurable_snd))
  have he : Phase.anchor (n:=n) = f ∘ Phase.code := by funext p; cases p <;> rfl
  rw [he]
  exact hf.comp phase_code_measurable

theorem phase_history_measurable : Measurable (Phase.history (n:=n)) := by
  let f : (Fin 3 × Anchor n) ⊕ (Fin 3 × Pending n × ℝ) → UpperCircularStage.History n :=
    Sum.elim (fun x => x.2.residue.history) (fun x => x.2.1.buffer.history)
  have hl : Measurable (fun x : Fin 3 × Anchor n => x.2.residue.history) :=
    UpperCorrectionExecution.state_history_measurable.comp (anchor_residue_measurable.comp measurable_snd)
  have hr : Measurable (fun x : Fin 3 × Pending n × ℝ => x.2.1.buffer.history) :=
    UpperCorrectionExecution.state_history_measurable.comp (pending_buffer_measurable.comp
      (measurable_fst.comp measurable_snd))
  have hf : Measurable f := hl.sumElim hr
  have he : Phase.history (n:=n) = f ∘ Phase.code := by funext p; cases p <;> rfl
  rw [he]
  exact hf.comp phase_code_measurable

end EnvyFreeResearch.Full.UpperGlobalPhysical
