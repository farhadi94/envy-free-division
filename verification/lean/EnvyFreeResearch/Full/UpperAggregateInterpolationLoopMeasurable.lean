import EnvyFreeResearch.Full.UpperAggregateInterpolationParameterized
import EnvyFreeResearch.Full.UpperAggregateInterpolationLoop

/-! Joint Borel charge of the actual loop with a grid-dependent initial
history, job table, and immutable endpoint error function. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperCorrectionExecution UpperCorrectionLoop UpperDomainDifference
  UpperCircularStage UpperStageMeasurable

variable {X : Type*} [MeasurableSpace X] {n m : ℕ}

theorem loopTransition_family_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin m → Job n) (hjobs : ∀ i, Measurable (fun x => jobs x i)) (i : Fin m) :
    Measurable (fun p : (X × LoopState n) × Start => loopTransition policy (jobs p.1.1) i p.1.2 p.2) :=
  measurable_snd.comp ((UpperCorrectionLoop.step_measurable policy hpolicy).comp
    ((measurable_snd.comp measurable_fst).prodMk
      (((hjobs i).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))

theorem proposalCharge_family_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin m → Job n) (hjobs : ∀ i, Measurable (fun x => jobs x i))
    (u : X → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u)) (i : Fin m) :
    Measurable (fun p : (X × LoopState n) × Start => proposalCharge policy (jobs p.1.1 i) (u p.1.1) p.1.2 p.2) := by
  have hstate : Measurable (fun p : (X × LoopState n) × Start => p.1.2) := measurable_snd.comp measurable_fst
  have hparam : Measurable (fun p : (X × LoopState n) × Start => p.1.1) := measurable_fst.comp measurable_fst
  have hjob := (hjobs i).comp hparam
  have hr := descriptor_measurable policy hpolicy
    (fun p : (X × LoopState n) × Start => p.1.2.current)
    (fun p => (jobs p.1.1 i).owner) (fun p => (jobs p.1.1 i).deficit) (fun p => p.2)
    (loop_current_measurable.comp hstate) (job_owner_measurable.comp hjob)
    (job_deficit_measurable.comp hjob) measurable_snd
  exact measurable_const.ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp hstate) measurable_const)
    ((hu.comp (hparam.prodMk (correction_first_measurable.comp hr))).add
      (hu.comp (hparam.prodMk (correction_last_measurable.comp hr))))

theorem loop_charge_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : X → Fin m → Job n) (hjobs : ∀ i, Measurable (fun x => jobs x i))
    (u : X → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u))
    (initial : X → LoopState n) (hinitial : Measurable initial) :
    Measurable (fun p : X × (Fin m → Start) => tapeTotal (loopTransition policy (jobs p.1))
      (fun i => proposalCharge policy (jobs p.1 i) (u p.1)) (initial p.1) p.2) :=
  parameterized_tapeTotal_measurable (fun x => loopTransition policy (jobs x))
    (fun x i => proposalCharge policy (jobs x i) (u x))
    (loopTransition_family_measurable policy hpolicy jobs hjobs)
    (proposalCharge_family_measurable policy hpolicy jobs hjobs u hu) initial hinitial

/-- Markov with an almost-everywhere event inclusion, so null sampling-grid
exceptions need not be added to the reported failure probability. -/
theorem common_lintegral_probability_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (charge : Ω → ℝ≥0∞) (hcharge : AEMeasurable charge μ) (bad : Set Ω)
    (C b : ℝ) (hb : 0 < b) (hmean : (∫⁻ ω, charge ω ∂μ) ≤ ENNReal.ofReal C)
    (hbad : ∀ᵐ ω ∂μ, ω ∈ bad → ENNReal.ofReal (b / (1 + b)) ≤ charge ω) :
    μ bad ≤ ENNReal.ofReal (C * (1 + b) / b) := by
  have ht : 0 < b / (1 + b) := div_pos hb (by linarith)
  calc
    μ bad ≤ μ {ω | ENNReal.ofReal (b / (1 + b)) ≤ charge ω} := measure_mono_ae hbad
    _ ≤ (∫⁻ ω, charge ω ∂μ) / ENNReal.ofReal (b / (1 + b)) :=
      meas_ge_le_lintegral_div hcharge (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (b / (1 + b)) := by gcongr
    _ = ENNReal.ofReal (C / (b / (1 + b))) := (ENNReal.ofReal_div_of_pos ht).symm
    _ = _ := by congr 1; field_simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
