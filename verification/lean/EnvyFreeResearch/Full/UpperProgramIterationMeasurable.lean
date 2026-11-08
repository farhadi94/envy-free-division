import EnvyFreeResearch.Full.ProgramMeasurable
import EnvyFreeResearch.Full.UpperProgramIteration

/-! Borel certification of finite query-program iteration, retaining the
original parameter jointly with every returned intermediate state. -/

noncomputable section

open MeasureTheory

namespace EnvyFreeResearch.Full.UpperProgramIterationMeasurable

open Chores.QueryProgram ProgramMeasurable UpperQueryPrograms UpperProgramIteration

variable {n : ℕ} {Parameter State Draw Sample : Type}
  [MeasurableSpace Parameter] [MeasurableSpace State] [MeasurableSpace Draw] [MeasurableSpace Sample]

theorem runProgram_certified
    (step : Parameter → State → Draw → QProgram n (Sample × State))
    (hstep : Certified (fun z : Parameter × State × Draw => step z.1 z.2.1 z.2.2))
    (m : ℕ) :
    Certified (fun z : Parameter × State × (Fin m → Draw) =>
      runProgram (step z.1) m z.2.1 z.2.2) := by
  induction m with
  | zero =>
    exact Certified.returned _ (measurable_const.prodMk (measurable_fst.comp measurable_snd))
  | succ m ih =>
    have hfirst := hstep.comp
      (fun z : Parameter × State × (Fin (m + 1) → Draw) => (z.1, z.2.1, z.2.2 0))
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))
    have hdraw : Measurable (fun z : (Parameter × State × (Fin (m + 1) → Draw)) × (Sample × State) =>
        fun i : Fin m => z.1.2.2 i.succ) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply i.succ).comp
        (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hrest := ih.comp
      (fun z : (Parameter × State × (Fin (m + 1) → Draw)) × (Sample × State) =>
        (z.1.1, z.2.2, fun i => z.1.2.2 i.succ))
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_snd).prodMk hdraw))
    have hvalues : Measurable (fun z :
        ((Parameter × State × (Fin (m + 1) → Draw)) × (Sample × State)) × ((Fin m → Sample) × State) =>
        Fin.cons (α := fun _ : Fin (m + 1) => Sample) z.1.2.1 z.2.1) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst.comp (measurable_snd.comp measurable_fst)
      · exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    have htail := hrest.bind (fun z => Program.returned (Fin.cons (α := fun _ : Fin (m + 1) => Sample) z.1.2.1 z.2.1, z.2.2))
      (Certified.returned _ (hvalues.prodMk (measurable_snd.comp measurable_snd)))
    exact hfirst.bind _ htail

theorem runProgram_family_certified {X : Type} [MeasurableSpace X]
    (step : Parameter → State → Draw → QProgram n (Sample × State))
    (hstep : Certified (fun z : Parameter × State × Draw => step z.1 z.2.1 z.2.2))
    (m : ℕ) (parameter : X → Parameter) (state : X → State) (draw : X → Fin m → Draw)
    (hparameter : Measurable parameter) (hstate : Measurable state)
    (hdraw : ∀ i, Measurable (fun x => draw x i)) :
    Certified (fun x => runProgram (step (parameter x)) m (state x) (draw x)) :=
  (runProgram_certified step hstep m).comp (fun x => (parameter x, state x, draw x))
    (hparameter.prodMk (hstate.prodMk (Measurable.of_eval hdraw)))

end EnvyFreeResearch.Full.UpperProgramIterationMeasurable
