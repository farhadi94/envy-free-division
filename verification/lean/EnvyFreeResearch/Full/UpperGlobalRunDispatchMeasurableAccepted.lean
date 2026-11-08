import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurable
import EnvyFreeResearch.Full.UpperGlobalRunTerminationMeasurable

/-! The actual acceptance bit and successful-call events are Borel on the
original execution stream, with no validity or acceptance conditioning. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperStageMeasurable
open UpperZeroRows UpperGlobalNormalize
open scoped Classical
variable {n : ℕ}

def acceptedAt (active : Finset (Fin n)) (policy : Policy n) (chores : Bool)
    (phase : Phase n) (draw : Universal n) : Bool :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    phaseCases (fun _ _ => false)
      (fun a draw => !(UpperSnapshotProtocol.snapshotExecute policy hk chores (enumerate active)
        a.residue ⟨0,by omega⟩ (snapshotTape active (by omega) draw)).2.2)
      (fun _ _ => false)
      (fun p G draw => !(UpperShrink.execute policy (by omega) chores (enumerate active)
        p.buffer G (shrinkTape active (by omega) draw)).2.2)
      (fun p draw => !(UpperShrink.execute policy (by omega) chores (enumerate active)
        p.buffer (2/UpperRepair.nearError n) (shrinkTape active (by omega) draw)).2.2)
      (fun p draw => !(repairResultAt active policy (by omega) chores p
        (repairTape active (by omega) draw)).2.2) phase draw
  else false

theorem acceptedAt_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (Function.uncurry (acceptedAt active policy chores)) := by
  change Measurable (fun z : Phase n × Universal n => acceptedAt active policy chores z.1 z.2)
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    simp only [Function.uncurry,acceptedAt,dite_eq_left hk]
    have hnot : Measurable Bool.not := measurable_of_countable _
    apply phaseCases_measurable
    · exact measurable_const
    · have hresult := UpperSnapshotProtocol.snapshotExecute_measurable policy hpolicy hk chores
        (enumerate active) (fun z : Anchor n × Universal n => z.1.residue) ⟨0,by omega⟩
        (fun z => snapshotTape active (by omega) z.2)
        (anchor_residue_measurable.comp measurable_fst)
        ((snapshotTape_measurable active (by omega)).comp measurable_snd)
      exact hnot.comp (measurable_snd.comp (measurable_snd.comp hresult))
    · exact measurable_const
    · have hresult := UpperShrink.execute_measurable policy hpolicy (by omega) chores
        (enumerate active) (fun z : (Pending n × ℝ) × Universal n => z.1.1.buffer)
        (fun z => z.1.2) (fun z => shrinkTape active (by omega) z.2)
        (pending_buffer_measurable.comp (measurable_fst.comp measurable_fst))
        (measurable_snd.comp measurable_fst) ((shrinkTape_measurable active (by omega)).comp measurable_snd)
      exact hnot.comp (measurable_snd.comp (measurable_snd.comp hresult))
    · have hresult := UpperShrink.execute_measurable policy hpolicy (by omega) chores
        (enumerate active) (fun z : Pending n × Universal n => z.1.buffer)
        (fun _ => 2/UpperRepair.nearError n) (fun z => shrinkTape active (by omega) z.2)
        (pending_buffer_measurable.comp measurable_fst) measurable_const
        ((shrinkTape_measurable active (by omega)).comp measurable_snd)
      exact hnot.comp (measurable_snd.comp (measurable_snd.comp hresult))
    · have hresult := (repairResultAt_measurable active policy hpolicy (by omega) chores).comp
        (measurable_fst.prodMk ((repairTape_measurable active (by omega)).comp measurable_snd))
      exact hnot.comp (measurable_snd.comp (measurable_snd.comp hresult))
  · simp only [Function.uncurry,acceptedAt,dite_eq_right hk]
    exact measurable_const

theorem acceptedAt_eq (policy : Policy n) (chores : Bool) (phase : Phase n) (draw : Universal n) :
    acceptedAt phase.anchor.active policy chores phase draw = Phase.accepted policy chores phase draw := by
  cases phase <;> dsimp only [Phase.anchor] <;> unfold acceptedAt <;> split <;>
    simp_all only [Phase.accepted,dite_true,dite_false,ite_true,ite_false,phaseCases]
  all_goals rfl

theorem accepted_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (Function.uncurry (Phase.accepted policy chores)) := by
  have h := finite_select_measurable
    (fun z : Phase n × Universal n => z.1.anchor.active)
    (anchor_active_measurable.comp (phase_anchor_measurable.comp measurable_fst))
    (fun active z => acceptedAt active policy chores z.1 z.2)
    (fun active => acceptedAt_measurable active policy hpolicy chores)
  convert h using 1
  funext z
  exact (acceptedAt_eq policy chores z.1 z.2).symm

theorem successEvent_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) (kind : Kind) (t : ℕ) :
    MeasurableSet (successEvent policy fallback chores initial kind t) := by
  have hstep := step_measurable policy hpolicy fallback chores
  have hrun := UpperGlobalRun.run_measurable (Phase.step policy fallback chores) hstep initial t
  exact (paidEvent_measurable policy fallback chores hstep initial kind t).inter
    (measurableSet_eq_fun ((accepted_measurable policy hpolicy chores).comp
      (hrun.prodMk (measurable_pi_apply t))) measurable_const)

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
