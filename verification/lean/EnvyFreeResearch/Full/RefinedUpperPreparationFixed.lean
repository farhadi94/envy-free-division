import EnvyFreeResearch.Full.RefinedUpperPreparationProgram

/-! A fixed recorded origin may be paired with every sampler tape without
unfolding the physical sampler during measurable-map elaboration. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n k : ℕ}

theorem prepare_fixed_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (q m : ℕ) :
    Measurable (fun x : Fin m → Fin k × I => UpperGridMerge.prepare policy active origin q m x) := by
  have hpair : Measurable (fun x : Fin m → Fin k × I => (origin,x)) :=
    measurable_const.prodMk measurable_id
  have h := (UpperGridMerge.prepare_measurable policy hmeas active q m).comp hpair
  change Measurable (fun x : Fin m → Fin k × I => UpperGridMerge.prepare policy active origin q m x) at h
  exact h

end EnvyFreeResearch.Full.RefinedUpperPreparation
