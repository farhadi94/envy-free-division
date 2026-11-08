import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointFamily
import EnvyFreeResearch.Full.UpperSnapshotRepetitionPacket

noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable
variable {X State Draw Output : Type} [MeasurableSpace X] [MeasurableSpace State]
  [MeasurableSpace Draw] [MeasurableSpace Output]

theorem run_family_measurable (step : X → State → Draw → State × Option Output)
    (hstep : Measurable (fun p : X × (State × Draw) => step p.1 p.2.1 p.2.2)) (m : ℕ) :
    Measurable (fun p : X × (State × Tape Draw m) => run (step p.1) (drawList p.2.2) p.2.1) := by
  induction m with
  | zero => exact (measurable_fst.comp measurable_snd).prodMk measurable_const
  | succ m ih =>
    have hsd : Measurable (fun p : X × (State × (Draw × Tape Draw m)) => (p.1,(p.2.1,p.2.2.1))) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    have hs := hstep.comp hsd
    have hnext : Measurable (fun p : X × (State × (Draw × Tape Draw m)) =>
        (p.1,((step p.1 p.2.1 p.2.2.1).1,p.2.2.2))) :=
      measurable_fst.prodMk ((measurable_fst.comp hs).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    exact measurable_option_cases (present := fun (p : X × (State × (Draw × Tape Draw m))) (a : Output) => ((step p.1 p.2.1 p.2.2.1).1,some a))
      (absent := fun (p : X × (State × (Draw × Tape Draw m))) => run (step p.1) (drawList p.2.2.2) (step p.1 p.2.1 p.2.2.1).1)
      (measurable_snd.comp hs)
      (((measurable_fst.comp hs).comp measurable_fst).prodMk (measurable_some.comp measurable_snd))
      (ih.comp hnext)

theorem packetStep_family_measurable (step : X → State → Draw → State × Option Output)
    (hstep : Measurable (fun p : X × (State × Draw) => step p.1 p.2.1 p.2.2)) :
    Measurable (fun p : X × (State × Draw) => packetStep (step p.1) p.2.1 p.2.2) := by
  have hp := measurable_option_cases
    (present := fun p a => some (p.2.1,p.2.2,a))
    (absent := fun _ : X × (State × Draw) => (none : Option (Packet State Draw Output)))
    (measurable_snd.comp hstep)
    (measurable_some.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))) measurable_const
  convert (measurable_fst.comp hstep).prodMk hp using 1
  funext p
  simp only [packetStep,Function.comp_def]
  cases (step p.1 p.2.1 p.2.2).2 <;> rfl

end EnvyFreeResearch.Full.UpperSnapshotRepetition
