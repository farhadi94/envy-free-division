import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointsCharge
import EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable
import EnvyFreeResearch.Full.UpperRecordedGrid

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable
variable {State Draw : Type} {L : ℕ}

def endpointVector (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (m : ℕ) (s : State) (tape : Tape Draw m) : Fin (m*L) → ℝ :=
  fun j => ((endpoints next reject points m s tape)[j.val]?).getD 0

theorem endpoints_measurable [MeasurableSpace State] [MeasurableSpace Draw]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ)
    (hn : Measurable (Function.uncurry next)) (hr : Measurable (Function.uncurry reject))
    (hp : ∀ j, Measurable (fun p : State × Draw => points p.1 p.2 j)) (m : ℕ) :
    Measurable (fun p : State × Tape Draw m => endpoints next reject points m p.1 p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have hsd : Measurable (fun p : State × (Draw × Tape Draw m) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hnext : Measurable (fun p : State × (Draw × Tape Draw m) => (next p.1 p.2.1,p.2.2)) :=
      (hn.comp hsd).prodMk (measurable_snd.comp measurable_snd)
    exact measurable_list_append.comp
      (((UpperRecordedGrid.ofFn_measurable L).comp (Measurable.of_eval (fun j => (hp j).comp hsd))).prodMk
        ((ih.comp hnext).ite (measurableSet_eq_fun (hr.comp hsd) measurable_const) measurable_const))

theorem endpointVector_measurable [MeasurableSpace State] [MeasurableSpace Draw]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ)
    (hn : Measurable (Function.uncurry next)) (hr : Measurable (Function.uncurry reject))
    (hp : ∀ j, Measurable (fun p : State × Draw => points p.1 p.2 j)) (m : ℕ) (j : Fin (m*L)) :
    Measurable (fun p : State × Tape Draw m => endpointVector next reject points m p.1 p.2 j) :=
  UpperCorrectionOutputMeasurable.getD_measurable _
    ((measurable_list_getElem j.val).comp (endpoints_measurable next reject points hn hr hp m)) 0

theorem endpointVector_ofFn (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (m : ℕ) (s : State) (tape : Tape Draw m) :
    List.ofFn (endpointVector next reject points m s tape) = endpoints next reject points m s tape := by
  apply List.ext_getElem
  · simp [endpoints_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, endpointVector]
    rw [List.getElem?_eq_getElem hj]
    rfl

theorem endpointVector_charge (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞) (hu0 : u 0=0)
    (m : ℕ) (s : State) (tape : Tape Draw m) :
    (∑ j, u (endpointVector next reject points m s tape j)) = endpointCharge next reject points u m s tape := by
  rw [← List.sum_ofFn]
  change (List.ofFn (u ∘ endpointVector next reject points m s tape)).sum = _
  rw [← List.map_ofFn, endpointVector_ofFn]
  exact endpoints_charge next reject points u hu0 m s tape

end EnvyFreeResearch.Full.UpperSnapshotRepetition
