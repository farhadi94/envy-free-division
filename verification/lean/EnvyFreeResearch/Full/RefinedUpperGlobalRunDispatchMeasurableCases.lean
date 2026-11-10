import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeMeasurableState
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMachineMeasurable

/-! Borel elimination of the concrete six-constructor physical phase code. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
open MeasureTheory RefinedUpperGlobalPhysical RefinedUpperGlobalNormalize ProtocolMeasurable
variable {n : ℕ} {Draw Output : Type} [MeasurableSpace Draw] [MeasurableSpace Output]

def phaseCases (normalize snapshot done : Anchor n → Draw → Output)
    (first : Pending n → ℝ → Draw → Output) (second repair : Pending n → Draw → Output)
    (phase : Phase n) (draw : Draw) : Output :=
  match phase with
  | .normalize a => normalize a draw
  | .snapshot a => snapshot a draw
  | .done a => done a draw
  | .firstShrink p G => first p G draw
  | .secondShrink p => second p draw
  | .finalRepair p => repair p draw

theorem phaseCases_measurable
    (normalize snapshot done : Anchor n → Draw → Output)
    (first : Pending n → ℝ → Draw → Output) (second repair : Pending n → Draw → Output)
    (hn : Measurable (Function.uncurry normalize))
    (hs : Measurable (Function.uncurry snapshot))
    (hd : Measurable (Function.uncurry done))
    (hf : Measurable (fun z : (Pending n × ℝ) × Draw => first z.1.1 z.1.2 z.2))
    (hsecond : Measurable (Function.uncurry second))
    (hr : Measurable (Function.uncurry repair)) :
    Measurable (Function.uncurry (phaseCases normalize snapshot done first second repair)) := by
  let left := fun draw : Draw => fun p : Fin 3 × Anchor n =>
    if p.1=0 then normalize p.2 draw else if p.1=1 then snapshot p.2 draw else done p.2 draw
  let right := fun draw : Draw => fun p : Fin 3 × Pending n × ℝ =>
    if p.1=0 then first p.2.1 p.2.2 draw
    else if p.1=1 then second p.2.1 draw else repair p.2.1 draw
  have hl : Measurable (fun z : Draw × (Fin 3 × Anchor n) => left z.1 z.2) := by
    have hm : Measurable (fun z : Draw × (Fin 3 × Anchor n) => (z.2.2,z.1)) :=
      (measurable_snd.comp measurable_snd).prodMk measurable_fst
    exact (hn.comp hm).ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      ((hs.comp hm).ite
        (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const) (hd.comp hm))
  have hright : Measurable (fun z : Draw × (Fin 3 × Pending n × ℝ) => right z.1 z.2) := by
    have hm : Measurable (fun z : Draw × (Fin 3 × Pending n × ℝ) => (z.2.2.1,z.1)) :=
      (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk measurable_fst
    exact (hf.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      ((hsecond.comp hm).ite
        (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const) (hr.comp hm))
  have h := (measurable_prod_sum_cases hl hright).comp
    (measurable_snd.prodMk ((comap_measurable Phase.code).comp measurable_fst))
  convert h using 1
  funext z
  rcases z with ⟨phase,draw⟩
  cases phase <;> rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
