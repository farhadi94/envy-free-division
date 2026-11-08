import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionMeasurable

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open UpperGlobal.Transfer
variable {n : ℕ}

def Pending.firstFactorAt (p : Pending n) (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (direction : Direction) : ℝ :=
  let j := activeIndex active p.target
  factor (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
    (factorIndex (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
      (fun i => (p.selectionDataAt active direction).2.1 i j/(p.selectionDataAt active direction).2.2 i) j).val

theorem firstFactorAt_eq (p : Pending n) [Nonempty (Fin p.anchor.active.card)] (direction : Direction) :
    p.firstFactorAt p.anchor.active direction=p.firstFactor direction := rfl

set_option maxHeartbeats 800000 in
theorem firstFactorAt_measurable (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (direction : Direction) : Measurable (fun p : Pending n => p.firstFactorAt active direction) := by
  have hdata := selectionDataAt_measurable active direction
  have hF (j : Fin active.card) : Measurable (fun p : Pending n =>
      factor (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
        (factorIndex (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
          (fun i => (p.selectionDataAt active direction).2.1 i j/(p.selectionDataAt active direction).2.2 i) j).val) := by
    have hratio : Measurable (fun p : Pending n => fun i =>
        (p.selectionDataAt active direction).2.1 i j/(p.selectionDataAt active direction).2.2 i) :=
      Measurable.of_eval (fun i => ((Selection.gap_measurable i j).comp hdata).div
        ((Selection.residue_measurable i).comp hdata))
    exact (Measurable.of_discrete : Measurable (fun e : Fin active.card =>
      factor (UpperShrinkPrecision.theta n) (UpperRepair.nearError n) e.val)).comp
      ((factorIndex_measurable _ _ j).comp hratio)
  have hh : Measurable (fun x : Pending n × Fin active.card =>
      factor (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
        (factorIndex (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
          (fun i => (x.1.selectionDataAt active direction).2.1 i x.2/(x.1.selectionDataAt active direction).2.2 i) x.2).val) :=
    measurable_from_prod_countable_left hF
  have ht : Measurable (fun p : Pending n => activeIndex active p.target) :=
    (Measurable.of_discrete : Measurable (activeIndex active)).comp pending_target_measurable
  simpa only [Pending.firstFactorAt,Function.comp_def,id_eq] using hh.comp (measurable_id.prodMk ht)

def Pending.transferCandidateAt (p : Pending n) (active : Finset (Fin n)) :
    Selection.Candidate active.card → Pending n
  | .commit alpha b h => p.transfer (extendPermutation active alpha) (enumerate active b) (enumerate active h)
  | .shrink b h => p.transfer (Equiv.refl _) (enumerate active b) (enumerate active h)

def Pending.dispatchTransferAt (p : Pending n) (active : Finset (Fin n)) :
    Selection.Candidate active.card → Phase n
  | c@(.commit _ _ _) => .finalRepair (p.transferCandidateAt active c)
  | c@(.shrink _ _) => .secondShrink (p.transferCandidateAt active c)

def Pending.selectPhaseAt (p : Pending n) (active : Finset (Fin n)) (direction : Direction) : Option (Phase n) :=
  (Selection.select (UpperRepair.nearError n) (p.selectionDataAt active direction)).map (p.dispatchTransferAt active)

theorem transferCandidateAt_eq (p : Pending n) (c : Selection.Candidate p.anchor.active.card) :
    p.transferCandidateAt p.anchor.active c=p.transferCandidate c := by cases c <;> rfl

theorem dispatchTransferAt_eq (p : Pending n) (c : Selection.Candidate p.anchor.active.card) :
    p.dispatchTransferAt p.anchor.active c=p.dispatchTransfer c := by cases c <;> rfl

theorem transferCandidateAt_measurable (active : Finset (Fin n)) (c : Selection.Candidate active.card) :
    Measurable (fun p : Pending n => p.transferCandidateAt active c) := by
  cases c <;> exact pending_mk_measurable _ _ _ _ _ _ _ pending_anchor_measurable pending_snapshot_measurable
    pending_shrunk_measurable pending_buffer_measurable measurable_const measurable_const measurable_const

theorem dispatchTransferAt_measurable (active : Finset (Fin n)) (c : Selection.Candidate active.card) :
    Measurable (fun p : Pending n => p.dispatchTransferAt active c) := by
  cases c with
  | commit alpha b h => exact phase_finalRepair_measurable.comp (transferCandidateAt_measurable active (.commit alpha b h))
  | shrink b h => exact phase_secondShrink_measurable.comp (transferCandidateAt_measurable active (.shrink b h))

theorem selectPhaseAt_measurable (active : Finset (Fin n)) (direction : Direction) :
    Measurable (fun p : Pending n => p.selectPhaseAt active direction) := by
  have hh : Measurable (fun x : Pending n × Option (Selection.Candidate active.card) =>
      x.2.map (x.1.dispatchTransferAt active)) := by
    apply measurable_from_prod_countable_left
    intro c
    cases c with
    | none => exact measurable_const
    | some c => exact ProtocolMeasurable.measurable_some.comp (dispatchTransferAt_measurable active c)
  exact hh.comp (measurable_id.prodMk (selectTransferAt_measurable active direction))

end EnvyFreeResearch.Full.UpperGlobalPhysical
