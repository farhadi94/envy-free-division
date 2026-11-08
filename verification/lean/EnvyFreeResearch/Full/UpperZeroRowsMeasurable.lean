import EnvyFreeResearch.Full.UpperPopulationZero

/-! Population decisions and zero-query terminal outputs are measurable
functions of the recorded state; no semantic measure inspection occurs. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperDomainDifference
variable {n : ℕ} {X : Type} [MeasurableSpace X]

theorem giveAll_measurable (origin : X → State n) (horigin : Measurable origin)
    (recipient j : Fin n) : Measurable (fun x => giveAll (origin x) recipient j) := by
  unfold giveAll
  split_ifs
  · exact horigin
  · exact empty_measurable _ (state_history_measurable.comp horigin)

theorem zeroRows_measurable (origin : X → State n) (horigin : Measurable origin)
    (active : Finset (Fin n)) : Measurable (fun x => zeroRows (origin x) active) := by
  have hbits : Measurable (fun x (i : Fin n) => decide (total (origin x) i = 0)) := by
    apply measurable_pi_lambda
    intro i
    exact decide_measurable _ (measurableSet_eq_fun
      (total_measurable origin (fun _ => i) horigin measurable_const) measurable_const)
  have hfinite : Measurable (fun bits : Fin n → Bool => active.filter (fun i => bits i = true)) :=
    measurable_of_countable _
  simpa only [zeroRows, Function.comp_def, decide_eq_true_eq] using hfinite.comp hbits

theorem positiveRows_measurable (origin : X → State n) (horigin : Measurable origin)
    (active : Finset (Fin n)) : Measurable (fun x => positiveRows (origin x) active) :=
  (measurable_of_countable (fun zero : Finset (Fin n) => active \ zero)).comp
    (zeroRows_measurable origin horigin active)

end EnvyFreeResearch.Full.UpperZeroRows
