import EnvyFreeResearch.Full.NonnegativeMainEvents

namespace EnvyFreeResearch.Full.NonnegativeHardFamily

open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeExperiment
open NonnegativeRandomOutput NonnegativeRetainedFailure NonnegativeEndpointCapture
open NonnegativeDetection NonnegativeDecoderLedger NonnegativeProbability NonnegativeRealLedger
open NonnegativeMainEvents Filter
open scoped Classical ENNReal Topology

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

noncomputable def expectedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) : ℝ≥0∞ :=
  ∫⁻ tape, (queryCost next (flaggedOracle flag uniform) tape [] : ℝ≥0∞) ∂μ

theorem actual_failure_real_le (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (h p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfixed : ∀ input : Input n, ENNReal.ofReal p ≤
      μ (eventualSuccess next (inputOracle flag h input) []
        {A | Fair chores (inputRows h input) A})) :
    (μ.prod (perturbLaw n w)).real (failure next flag chores h) ≤ 1 - p := by
  let := perturbLaw_probability n hn w hw
  have hsuccess := measurable_jointSuccess next (inputOracle flag h) hnext
    (inputOracle_measurable flag h) [] (inputGood chores h) (inputGood_measurable chores h)
  have hbound := fixed_input_failure_bound μ (perturbLaw n w) next (inputOracle flag h) hnext
    (inputOracle_measurable flag h) [] (inputGood chores h) (inputGood_measurable chores h)
    (ENNReal.ofReal p) hfixed
  have hswap : (μ.prod (perturbLaw n w)) (failure next flag chores h) =
      ((perturbLaw n w).prod μ) (jointSuccess next (inputOracle flag h) [] (inputGood chores h))ᶜ :=
    (Measure.measurePreserving_swap (μ := μ) (ν := perturbLaw n w)).measure_preimage
      hsuccess.compl.nullMeasurableSet
  have hbound' : (μ.prod (perturbLaw n w)) (failure next flag chores h) ≤ 1 - ENNReal.ofReal p := by
    rw [hswap]
    exact hbound
  have hfinite : 1 - ENNReal.ofReal p ≠ ∞ := ne_top_of_le_ne_top (by simp) tsub_le_self
  have hreal := ENNReal.toReal_mono hfinite hbound'
  have hpENN : ENNReal.ofReal p ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1
  simpa only [Measure.real, ENNReal.toReal_sub_of_le hpENN (by simp : (1 : ℝ≥0∞) ≠ ∞),
    ENNReal.toReal_one, ENNReal.toReal_ofReal hp0] using hreal

/-- The exact quantitative retention inequality for a concrete capped
baseline and one concrete pulse width. The only losses are the actual
geometric loss and actual cap exhaustion. All detector, decoder and replay
premises have been instantiated by the physical experiment. -/
theorem capped_retained_lower [NeZero n]
    (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (fuel : ℕ) (h p : ℝ) (hh : 0 < h) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfinite : expectedCost μ next flag ≠ ∞)
    (hfixed : ∀ input : Input n, ENNReal.ofReal p ≤
      μ (eventualSuccess next (inputOracle flag h input) []
        {A | Fair chores (inputRows h input) A})) :
    R8Lower.retainedQueryLower n
      (p - (μ.prod (perturbLaw n w)).real (geometricLoss next flag fuel h) -
        (μ.prod (perturbLaw n w)).real (capLoss next flag fuel)) w ≤
      (expectedCost μ next flag).toReal := by
  have hn0 : 0 < n := by omega
  let := perturbLaw_probability n hn0 w hw
  let ρ := μ.prod (perturbLaw n w)
  have hS := success_measurable next hnext flag fuel
  have hD := measurable_decoded (baseline next flag fuel) (baseline_measurable next hnext flag fuel) chores
  have hretained := retained_failure_mass (μ := ρ) hS hD
    (decoded_subset_success (baseline next flag fuel) chores)
    (retained_event_inclusion next flag chores fuel h hh)
  have hSmeasure : ρ (success next flag fuel) =
      μ {tape | Successful {A | UniformEF A} (baseline next flag fuel tape)} := by
    exact fst_lift_mass μ (perturbLaw n w)
      {tape | Successful {A | UniformEF A} (baseline next flag fuel tape)}
  have hSreal : ρ.real (success next flag fuel) =
      μ.real {tape | Successful {A | UniformEF A} (baseline next flag fuel tape)} :=
    congrArg ENNReal.toReal hSmeasure
  have hdecode := integrated_physical_decoder_real μ hn0 w hw hwsmall
    (baseline next flag fuel) (baseline_measurable next hnext flag fuel) chores
  rw [← hSreal] at hdecode
  have hdetect := actual_capped_detection_real_le μ hn0 w hw next uniform flag hnext
    uniformOracle_measurable (uniformFlagged_measurable flag) fuel
    {A | UniformEF A} measurable_uniformEF hfinite
  change ρ.real (detected next flag fuel) ≤ (w / (n : ℝ)) *
    ((expectedCost μ next flag).toReal +
      (1 - μ.real {tape | Successful {A | UniformEF A} (baseline next flag fuel tape)})) at hdetect
  rw [← hSreal] at hdetect
  have hfailure := actual_failure_real_le μ hn0 w hw next hnext flag chores h p hp0 hp1 hfixed
  have hloss : ρ.real (detected next flag fuel ∪ (geometricLoss next flag fuel h ∪ capLoss next flag fuel)) ≤
      ρ.real (detected next flag fuel) + ρ.real (geometricLoss next flag fuel h) +
        ρ.real (capLoss next flag fuel) := by
    have houter := measureReal_union_le (μ := ρ) (detected next flag fuel)
      (geometricLoss next flag fuel h ∪ capLoss next flag fuel)
    have hinner := measureReal_union_le (μ := ρ) (geometricLoss next flag fuel h) (capLoss next flag fuel)
    linarith
  apply R8Lower.query_lower_from_retention (n : ℝ) w (ρ.real (success next flag fuel))
    (p - ρ.real (geometricLoss next flag fuel h) - ρ.real (capLoss next flag fuel))
    (expectedCost μ next flag).toReal (1 - ρ.real (success next flag fuel))
    (by exact_mod_cast hn) hw hwsmall measureReal_le_one le_rfl
  linarith

end EnvyFreeResearch.Full.NonnegativeHardFamily

#print axioms EnvyFreeResearch.Full.NonnegativeHardFamily.actual_failure_real_le
#print axioms EnvyFreeResearch.Full.NonnegativeHardFamily.capped_retained_lower
