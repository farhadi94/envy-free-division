import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointVector

/-! Joint measurability in the preparation data and the later product tape.
All preparation data are retained unchanged throughout rejection repetition. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable
variable {X State Draw : Type} [MeasurableSpace X] [MeasurableSpace State] [MeasurableSpace Draw]
variable {L : ℕ}

theorem endpoints_family_measurable
    (next : X → State → Draw → State) (reject : X → State → Draw → Bool)
    (points : X → State → Draw → Fin L → ℝ)
    (hn : Measurable (fun p : X × (State × Draw) => next p.1 p.2.1 p.2.2))
    (hr : Measurable (fun p : X × (State × Draw) => reject p.1 p.2.1 p.2.2))
    (hp : ∀ j, Measurable (fun p : X × (State × Draw) => points p.1 p.2.1 p.2.2 j))
    (m : ℕ) : Measurable (fun p : X × (State × Tape Draw m) =>
      endpoints (next p.1) (reject p.1) (points p.1) m p.2.1 p.2.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have hsd : Measurable (fun p : X × (State × (Draw × Tape Draw m)) => (p.1,(p.2.1,p.2.2.1))) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    have hnext : Measurable (fun p : X × (State × (Draw × Tape Draw m)) =>
        (p.1,(next p.1 p.2.1 p.2.2.1,p.2.2.2))) :=
      measurable_fst.prodMk ((hn.comp hsd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    exact measurable_list_append.comp
      (((UpperRecordedGrid.ofFn_measurable L).comp (Measurable.of_eval (fun j => (hp j).comp hsd))).prodMk
        ((ih.comp hnext).ite (measurableSet_eq_fun (hr.comp hsd) measurable_const) measurable_const))

theorem endpointVector_family_measurable
    (next : X → State → Draw → State) (reject : X → State → Draw → Bool)
    (points : X → State → Draw → Fin L → ℝ)
    (hn : Measurable (fun p : X × (State × Draw) => next p.1 p.2.1 p.2.2))
    (hr : Measurable (fun p : X × (State × Draw) => reject p.1 p.2.1 p.2.2))
    (hp : ∀ j, Measurable (fun p : X × (State × Draw) => points p.1 p.2.1 p.2.2 j))
    (m : ℕ) (j : Fin (m*L)) : Measurable (fun p : X × (State × Tape Draw m) =>
      endpointVector (next p.1) (reject p.1) (points p.1) m p.2.1 p.2.2 j) :=
  UpperCorrectionOutputMeasurable.getD_measurable _
    ((measurable_list_getElem j.val).comp (endpoints_family_measurable next reject points hn hr hp m)) 0

end EnvyFreeResearch.Full.UpperSnapshotRepetition
