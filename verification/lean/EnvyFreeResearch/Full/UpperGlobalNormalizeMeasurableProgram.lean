import EnvyFreeResearch.Full.UpperGlobalNormalizeMeasurableCore
import EnvyFreeResearch.Full.UpperGlobalNormalizeProgram
import EnvyFreeResearch.Full.UpperGlobalProtocolMachineMeasurable

/-! Compositional Borel certificates for the actual normalization query
program, including the half-cut terminal branch and varying selected owners. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open MeasureTheory UpperGlobalPhysical UpperCorrectionExecution UpperBaseCases
open UpperQueryPrograms UpperCircularStage ProtocolMeasurable ProgramMeasurable Chores.QueryProgram
open scoped Classical
variable {n : ℕ} {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]

theorem fin_select_certified (index : X → Fin n) (hi : Measurable index)
    (p : Fin n → X → QProgram n Output) (hp : ∀ i, Certified (p i)) :
    Certified (fun x => p (index x) x) := by
  let branches : ℕ → X → QProgram n Output := fun j x =>
    if h : j<n then p ⟨j,h⟩ x else .failed
  have hb : ∀ j, Certified (branches j) := by
    intro j
    by_cases hj : j<n
    · simpa only [branches,dite_eq_left hj] using hp ⟨j,hj⟩
    · simpa only [branches,dite_eq_right hj] using
        (Certified.failed : Certified (fun _ : X => (Program.failed : QProgram n Output)))
  apply (Certified.natCases (fun x => (index x).val)
    ((measurable_of_countable Fin.val).comp hi) branches hb).congr
  intro x
  simp only [branches,dite_eq_left (index x).isLt]

def Request.twoData : Request n → Option (Anchor n × Fin n × Fin n)
  | .two a i j => some (a,i,j)
  | _ => none

def Request.idlePhase : Request n → Phase n
  | .snapshot a => .snapshot a
  | .done a | .two a _ _ => .done a

theorem twoData_measurable : Measurable (Request.twoData (n := n)) := by
  have h : Measurable (fun c : Anchor n ⊕ ((Anchor n × Fin n × Fin n) ⊕ Anchor n) =>
      c.elim (fun _ => none) (Sum.elim some (fun _ => none))) :=
    measurable_const.sumElim (measurable_some.sumElim measurable_const)
  convert h.comp (comap_measurable Request.code) using 1
  funext request
  cases request <;> rfl

theorem idlePhase_measurable : Measurable (Request.idlePhase (n := n)) := by
  have h : Measurable (fun c : Anchor n ⊕ ((Anchor n × Fin n × Fin n) ⊕ Anchor n) =>
      c.elim Phase.done (Sum.elim (fun p => Phase.done p.1) Phase.snapshot)) :=
    phase_done_measurable.sumElim
      ((phase_done_measurable.comp measurable_fst).sumElim phase_snapshot_measurable)
  convert h.comp (comap_measurable Request.code) using 1
  funext request
  cases request <;> rfl

theorem two_fixed_certified (chores : Bool) (cutter chooser : Fin n) :
    Certified (fun a : Anchor n => requestProgram chores (.two a cutter chooser)) := by
  change Certified (fun a : Anchor n => (halfProgram a.residue cutter).bind
    (fun out => .returned (Phase.done (terminal a (finish chores cutter chooser out) out.2.history))))
  refine (half_certified Anchor.residue anchor_residue_measurable cutter).bind
    (fun z => .returned (Phase.done (terminal z.1 (finish chores cutter chooser z.2) z.2.2.history))) ?_
  apply Certified.returned
  apply phase_done_measurable.comp
  exact terminal_measurable Prod.fst measurable_fst _
    (finish_measurable chores cutter chooser Prod.snd measurable_snd)
    _ (state_history_measurable.comp (measurable_snd.comp measurable_snd))

theorem requestProgram_certified (chores : Bool) :
    Certified (requestProgram (n := n) chores) := by
  have hp : Certified (fun z : Request n × (Anchor n × Fin n × Fin n) =>
      requestProgram chores (.two z.2.1 z.2.2.1 z.2.2.2)) := by
    refine fin_select_certified (fun z : Request n × (Anchor n × Fin n × Fin n) => z.2.2.1)
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (fun cutter z => requestProgram chores (.two z.2.1 cutter z.2.2.2)) ?_
    intro cutter
    refine fin_select_certified (fun z : Request n × (Anchor n × Fin n × Fin n) => z.2.2.2)
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
      (fun chooser z => requestProgram chores (.two z.2.1 cutter chooser)) ?_
    intro chooser
    exact (two_fixed_certified chores cutter chooser).comp
      (fun z : Request n × (Anchor n × Fin n × Fin n) => z.2.1) (measurable_fst.comp measurable_snd)
  apply (Certified.optionCases Request.twoData twoData_measurable _ _ hp
    (Certified.returned Request.idlePhase idlePhase_measurable)).congr
  intro request
  cases request <;> rfl

theorem program_certified (fallback : Fin n) (chores : Bool) :
    Certified (program fallback chores) :=
  (requestProgram_certified chores).comp _ (normalize_measurable fallback chores n)

theorem measurable_next (fallback : Fin n) (chores : Bool) :
    Measurable (fun z : Anchor n × History n => ((program fallback chores z.1).after z.2).action) :=
  (program_certified fallback chores).measurable_next

end EnvyFreeResearch.Full.UpperGlobalNormalize
