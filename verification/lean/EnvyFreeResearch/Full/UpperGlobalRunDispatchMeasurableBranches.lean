import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableSnapshot
import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableShrink
import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableRepair
import EnvyFreeResearch.Full.UpperGlobalRunDispatchMeasurableTapes
import EnvyFreeResearch.Full.UpperGlobalNormalizeMeasurableOutput

/-! Each actual paid branch reads the primitive tape for a fixed active set.
Finite conditioning on that set will recover the varying-population machine. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
open MeasureTheory UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperStageMeasurable
open scoped Classical
variable {n : ℕ}

def snapshotBranch (active : Finset (Fin n)) (policy : Policy n) (chores : Bool)
    (a : Anchor n) (draw : Universal n) : Phase n :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    snapshotAt active policy hk chores a (snapshotTape active (by omega) draw)
  else .done a

def firstBranch (active : Finset (Fin n)) (policy : Policy n) (chores : Bool)
    (p : Pending n) (G : ℝ) (draw : Universal n) : Phase n :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    firstShrinkAt active policy (by omega) chores p G (shrinkTape active (by omega) draw)
  else .done p.anchor

def secondBranch (active : Finset (Fin n)) (policy : Policy n) (chores : Bool)
    (p : Pending n) (draw : Universal n) : Phase n :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    secondShrinkAt active policy (by omega) chores p (shrinkTape active (by omega) draw)
  else .done p.anchor

def repairBranch (active : Finset (Fin n)) (policy : Policy n) (chores : Bool)
    (p : Pending n) (draw : Universal n) : Phase n :=
  if hk : 3 ≤ active.card then
    letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    repairAt active policy (by omega) chores p (repairTape active (by omega) draw)
  else .done p.anchor

theorem snapshotBranch_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (Function.uncurry (snapshotBranch active policy chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Anchor n × Universal n =>
        (z.1,snapshotTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((snapshotTape_measurable active (by omega)).comp measurable_snd)
    have h := (snapshotAt_measurable active policy hpolicy hk chores).comp hm
    convert h using 1
    funext z
    simp only [Function.uncurry,Function.comp_def,snapshotBranch,dite_eq_left hk]
  · have h : Measurable (fun z : Anchor n × Universal n => Phase.done z.1) :=
      phase_done_measurable.comp measurable_fst
    convert h using 1
    funext z
    simp only [Function.uncurry,snapshotBranch,dite_eq_right hk]

theorem firstBranch_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (fun z : (Pending n × ℝ) × Universal n => firstBranch active policy chores z.1.1 z.1.2 z.2) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : (Pending n × ℝ) × Universal n =>
        (z.1,shrinkTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((shrinkTape_measurable active (by omega)).comp measurable_snd)
    have h := (firstShrinkAt_measurable active policy hpolicy (by omega) chores).comp hm
    convert h using 1
    funext z
    simp only [Function.comp_def,firstBranch,dite_eq_left hk]
  · have h : Measurable (fun z : (Pending n × ℝ) × Universal n => Phase.done z.1.1.anchor) :=
      phase_done_measurable.comp (pending_anchor_measurable.comp (measurable_fst.comp measurable_fst))
    convert h using 1
    funext z
    simp only [firstBranch,dite_eq_right hk]

theorem secondBranch_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (Function.uncurry (secondBranch active policy chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Pending n × Universal n =>
        (z.1,shrinkTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((shrinkTape_measurable active (by omega)).comp measurable_snd)
    have h := (secondShrinkAt_measurable active policy hpolicy (by omega) chores).comp hm
    convert h using 1
    funext z
    simp only [Function.uncurry,Function.comp_def,secondBranch,dite_eq_left hk]
  · have h : Measurable (fun z : Pending n × Universal n => Phase.done z.1.anchor) :=
      phase_done_measurable.comp (pending_anchor_measurable.comp measurable_fst)
    convert h using 1
    funext z
    simp only [Function.uncurry,secondBranch,dite_eq_right hk]

theorem repairBranch_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (chores : Bool) :
    Measurable (Function.uncurry (repairBranch active policy chores)) := by
  by_cases hk : 3 ≤ active.card
  · letI : Nonempty (Fin active.card) := ⟨⟨0,by omega⟩⟩
    have hm : Measurable (fun z : Pending n × Universal n =>
        (z.1,repairTape active (by omega) z.2)) :=
      measurable_fst.prodMk ((repairTape_measurable active (by omega)).comp measurable_snd)
    have h := (repairAt_measurable active policy hpolicy (by omega) chores).comp hm
    convert h using 1
    funext z
    simp only [Function.uncurry,Function.comp_def,repairBranch,dite_eq_left hk]
  · have h : Measurable (fun z : Pending n × Universal n => Phase.done z.1.anchor) :=
      phase_done_measurable.comp (pending_anchor_measurable.comp measurable_fst)
    convert h using 1
    funext z
    simp only [Function.uncurry,repairBranch,dite_eq_right hk]

def stepAt (active : Finset (Fin n)) (policy : Policy n) (fallback : Fin n) (chores : Bool) :=
  phaseCases (fun a _ => UpperGlobalNormalize.execute policy fallback chores a)
    (snapshotBranch active policy chores) (fun a _ => Phase.done a)
    (firstBranch active policy chores) (secondBranch active policy chores) (repairBranch active policy chores)

theorem stepAt_measurable (active : Finset (Fin n)) (policy : Policy n)
    (hpolicy : MeasurablePolicy policy) (fallback : Fin n) (chores : Bool) :
    Measurable (Function.uncurry (stepAt active policy fallback chores)) :=
  phaseCases_measurable _ _ _ _ _ _
    ((UpperGlobalNormalize.execute_measurable policy hpolicy fallback chores).comp measurable_fst)
    (snapshotBranch_measurable active policy hpolicy chores)
    (phase_done_measurable.comp measurable_fst)
    (firstBranch_measurable active policy hpolicy chores)
    (secondBranch_measurable active policy hpolicy chores)
    (repairBranch_measurable active policy hpolicy chores)

end EnvyFreeResearch.Full.UpperGlobalRun.DispatchMeasurable
