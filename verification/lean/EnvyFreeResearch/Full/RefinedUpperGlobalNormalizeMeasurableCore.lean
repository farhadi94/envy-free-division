import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeMeasurableState

/-! The concrete bounded normalization recursion is Borel, including every
cached sink and zero-row decision. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open MeasureTheory RefinedUpperGlobalPhysical RefinedUpperGlobal.Sink
open scoped Classical
variable {n : ℕ}

def Request.code : Request n → Anchor n ⊕ ((Anchor n × Fin n × Fin n) ⊕ Anchor n)
  | .done a => .inl a
  | .two a i j => .inr (.inl (a,i,j))
  | .snapshot a => .inr (.inr a)

instance : MeasurableSpace (Request n) := MeasurableSpace.comap Request.code inferInstance

theorem request_done_measurable : Measurable (Request.done (n := n)) :=
  measurable_comap_iff.mpr measurable_inl

theorem request_two_measurable :
    Measurable (fun p : Anchor n × Fin n × Fin n => Request.two p.1 p.2.1 p.2.2) :=
  measurable_comap_iff.mpr (measurable_inr.comp measurable_inl)

theorem request_snapshot_measurable : Measurable (Request.snapshot (n := n)) :=
  measurable_comap_iff.mpr (measurable_inr.comp measurable_inr)

theorem positiveCore_measurable (fallback : Fin n) (chores : Bool) (fuel : ℕ) :
    Measurable (positiveCore fallback chores fuel) := by
  have hc : Measurable (fun a : Anchor n => a.active.card) :=
    (measurable_of_countable Finset.card).comp anchor_active_measurable
  have hp := (pick_measurable fallback).comp anchor_active_measurable
  induction fuel with
  | zero => exact request_snapshot_measurable
  | succ fuel ih =>
    exact (request_done_measurable.comp
      (giveAllTerminal_measurable _ hp id measurable_id)).ite
      (measurableSet_le hc measurable_const)
      ((request_two_measurable.comp (measurable_id.prodMk
        (hp.prodMk ((second_measurable fallback).comp anchor_active_measurable)))).ite
        (measurableSet_le hc measurable_const)
        ((ih.comp (selectedFreeze_measurable (direction chores))).ite
          ((sinkAvailable_measurable (direction chores)) (measurableSet_singleton true))
          request_snapshot_measurable))

theorem normalize_measurable (fallback : Fin n) (chores : Bool) (fuel : ℕ) :
    Measurable (normalize fallback chores fuel) := by
  have hnonempty : MeasurableSet {s : Finset (Fin n) | s.Nonempty} := Set.to_countable _ |>.measurableSet
  have hp := (pick_measurable fallback).comp anchor_active_measurable
  cases chores with
  | false =>
    change Measurable (fun a : Anchor n => if (UpperZeroRows.positiveRows a.residue a.active).Nonempty
      then positiveCore fallback false fuel (freezeZero a)
      else Request.done (giveAllTerminal a (pick fallback a.active)))
    exact ((positiveCore_measurable fallback false fuel).comp freezeZero_measurable).ite
      (anchor_positiveRows_measurable hnonempty)
      (request_done_measurable.comp (giveAllTerminal_measurable _ hp id measurable_id))
  | true =>
    change Measurable (fun a : Anchor n => if (UpperZeroRows.zeroRows a.residue a.active).Nonempty
      then Request.done (giveAllTerminal a (pick fallback (UpperZeroRows.zeroRows a.residue a.active)))
      else positiveCore fallback true fuel a)
    exact (request_done_measurable.comp (giveAllTerminal_measurable _
      ((pick_measurable fallback).comp anchor_zeroRows_measurable) id measurable_id)).ite
      (anchor_zeroRows_measurable hnonempty) (positiveCore_measurable fallback true fuel)

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
