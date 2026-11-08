import EnvyFreeResearch.Full.UpperGlobalRunTermination

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape
variable {n : ℕ}

theorem phase_paidKind_measurable : Measurable (Phase.paidKind (n:=n)) := by
  let left : Fin 3 → Option Kind := fun tag => if tag=1 then some .snapshot else none
  let right : Fin 3 → Option Kind := fun tag => if tag=2 then some .repair else some .shrink
  have hl : Measurable (fun p : Fin 3 × Anchor n => left p.1) :=
    (Measurable.of_discrete (f := left)).comp measurable_fst
  have hr : Measurable (fun p : Fin 3 × Pending n × ℝ => right p.1) :=
    (Measurable.of_discrete (f := right)).comp measurable_fst
  convert (hl.sumElim hr).comp (comap_measurable (Phase.code (n:=n))) using 1
  funext p
  cases p <;> simp [Phase.paidKind,Phase.code,left,right,Function.comp_def]

theorem phase_finished_measurable : Measurable (Phase.finished (n:=n)) := by
  let left : Fin 3 → Bool := fun tag => decide (tag=2)
  have hl : Measurable (fun p : Fin 3 × Anchor n => left p.1) :=
    (Measurable.of_discrete (f := left)).comp measurable_fst
  have hr : Measurable (fun _p : Fin 3 × Pending n × ℝ => false) := measurable_const
  convert (hl.sumElim hr).comp (comap_measurable (Phase.code (n:=n))) using 1
  funext p
  cases p <;> simp [Phase.finished,Phase.code,left,Function.comp_def]

theorem paidEvent_measurable (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (initial : Phase n) (kind : Kind) (t : ℕ) :
    MeasurableSet (paidEvent policy fallback chores initial kind t) := by
  let detect : Kind ⊕ Unit → Bool := Sum.elim (fun j => decide (j=kind)) (fun _ => false)
  have hd : Measurable detect := (Measurable.of_discrete (f := fun j : Kind => decide (j=kind))).sumElim measurable_const
  have hm := measurableSet_eq_fun
    (hd.comp (ProtocolMeasurable.measurable_optionCode.comp
      (phase_paidKind_measurable.comp (UpperGlobalRun.run_measurable _ hstep initial t))))
    (measurable_const (a := true))
  convert hm using 1
  ext omega
  change ((Phase.run policy fallback chores initial t omega).paidKind=some kind ↔
    detect (ProtocolMeasurable.optionCode ((Phase.run policy fallback chores initial t omega).paidKind))=true)
  cases he : (Phase.run policy fallback chores initial t omega).paidKind <;>
    simp [paidEvent,he,detect,ProtocolMeasurable.optionCode]

theorem allPaidEvent_measurable (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (initial : Phase n) (t : ℕ) :
    MeasurableSet (allPaidEvent policy fallback chores initial t) := by
  convert MeasurableSet.iUnion (fun kind => paidEvent_measurable policy fallback chores hstep initial kind t) using 1
  ext omega
  simp [allPaidEvent]

theorem finishedRun_measurable (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (initial : Phase n) : MeasurableSet {omega | finishedRun policy fallback chores initial omega} := by
  have ht : ∀ t, MeasurableSet {omega | (Phase.run policy fallback chores initial t omega).finished=true} :=
    fun t => measurableSet_eq_fun
      (phase_finished_measurable.comp (UpperGlobalRun.run_measurable _ hstep initial t)) measurable_const
  convert MeasurableSet.iUnion ht using 1
  ext omega
  simp [finishedRun]

end EnvyFreeResearch.Full.UpperGlobalPhysical
