import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunChancePhase
import EnvyFreeResearch.Full.RefinedUpperGlobalRunTerminationMeasurable
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolFiniteValidity

/-! Original-stream attempt inequalities obtained by integrating over actual
finite prefixes. Validity is proved pathwise, never conditioned upon or assumed
to be a measurable subset of the state space. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperStageMeasurable ProtocolMeasurable
variable {n : ℕ}

theorem paidKind_set_measurable (kind : Kind) :
    MeasurableSet {phase : Phase n | phase.paidKind=some kind} := by
  let detect : Kind ⊕ Unit → Bool := Sum.elim (fun j => decide (j=kind)) (fun _ => false)
  have hd : Measurable detect :=
    (Measurable.of_discrete (f := fun j : Kind => decide (j=kind))).sumElim measurable_const
  have h := measurableSet_eq_fun
    (hd.comp (measurable_optionCode.comp (phase_paidKind_measurable (n := n)))) (measurable_const (a := true))
  convert h using 1
  ext phase
  cases hp : phase.paidKind <;> simp [optionCode,hp,detect,Function.comp_def]

theorem finitePrefix_attempt_bound (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (haccept : Measurable (Function.uncurry (Phase.accepted policy chores)))
    (initial : Phase n) (kind : Kind) (t : ℕ) (factor : ℝ≥0∞) (hf : factor ≠ ∞)
    (hchance : ∀ pastDraws : Fin t → Universal n,
      (RefinedUpperGlobalRun.finiteRun (Phase.step policy fallback chores) initial t pastDraws).paidKind=some kind →
      1 ≤ factor * universalLaw n {draw | Phase.accepted policy chores
        (RefinedUpperGlobalRun.finiteRun (Phase.step policy fallback chores) initial t pastDraws) draw=true}) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial kind t) ≤
      factor * streamLaw (universalLaw n) (successEvent policy fallback chores initial kind t) := by
  let reached := RefinedUpperGlobalRun.finiteRun (Phase.step policy fallback chores) initial t
  have hm : Measurable reached := RefinedUpperGlobalRun.finiteRun_measurable _ hstep initial t
  let A : Set (Fin t → Universal n) := {pastDraws | (reached pastDraws).paidKind=some kind}
  let S : Set ((Fin t → Universal n) × Universal n) :=
    {z | (reached z.1).paidKind=some kind ∧ Phase.accepted policy chores (reached z.1) z.2=true}
  have hA : MeasurableSet A := (paidKind_set_measurable kind).preimage hm
  have hS : MeasurableSet S :=
    (hA.preimage measurable_fst).inter
      ((haccept.comp ((hm.comp measurable_fst).prodMk measurable_snd)) (measurableSet_singleton true))
  have hb := UpperExpectedRuntime.original_tape_attempt_bound
    (streamLaw (universalLaw n)) (prefixLaw (universalLaw n) t) (universalLaw n)
    _ (prefix_fresh_preserves (universalLaw n) t) A hA S hS factor hf (by
      intro pastDraws hp
      have he : {draw | (pastDraws,draw) ∈ S} =
          {draw | Phase.accepted policy chores (reached pastDraws) draw=true} := by
        ext draw
        simp only [S,mem_setOf_eq,show (reached pastDraws).paidKind=some kind from hp,true_and]
      rw [he]
      exact hchance pastDraws hp)
  rw [← (prefix_preserves (universalLaw n) t).measure_preimage hA.nullMeasurableSet] at hb
  exact hb

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
