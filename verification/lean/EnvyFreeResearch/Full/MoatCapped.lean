import EnvyFreeResearch.Full.MoatLimits

namespace EnvyFreeResearch.Full.MoatCapped
open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRandomOutput
open NonnegativeRetainedFailure NonnegativeEndpointCapture NonnegativeProbability
open NonnegativeMeasurableDetection NonnegativeExperiment NonnegativeHardFamily NonnegativeCostLedger
open MoatRetention
open scoped Classical ENNReal

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

theorem actual_failure_real_le (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (two flag chores : Bool) (h p : ℝ) (hh : 0 ≤ h) (hhw : h ≤ w) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfixed : ∀ input : MoatSelection.Input n, ENNReal.ofReal p ≤
      μ (eventualSuccess next (MoatExperiment.oracle two flag chores w h input) []
        {A | Fair chores (MoatExperiment.rows two chores w h input) A})) :
    (μ.prod (MoatDetection.law n)).real (MoatRetention.failure next two flag chores w h) ≤ 1 - p := by
  let := MoatDetection.law_probability n hn
  have hsuccess := measurable_jointSuccess next (MoatExperiment.oracle two flag chores w h) hnext
    (MoatExperiment.oracle_measurable two flag chores hw hh hhw) [] (MoatExperiment.inputGood two chores w h) (MoatExperiment.inputGood_measurable two chores w h)
  have hbound := fixed_input_failure_bound μ (MoatDetection.law n) next (MoatExperiment.oracle two flag chores w h) hnext
    (MoatExperiment.oracle_measurable two flag chores hw hh hhw) [] (MoatExperiment.inputGood two chores w h) (MoatExperiment.inputGood_measurable two chores w h)
    (ENNReal.ofReal p) hfixed
  have hswap : (μ.prod (MoatDetection.law n)) (MoatRetention.failure next two flag chores w h) =
      ((MoatDetection.law n).prod μ) (jointSuccess next (MoatExperiment.oracle two flag chores w h) [] (MoatExperiment.inputGood two chores w h))ᶜ :=
    (Measure.measurePreserving_swap (μ := μ) (ν := MoatDetection.law n)).measure_preimage
      hsuccess.compl.nullMeasurableSet
  have hbound' : (μ.prod (MoatDetection.law n)) (MoatRetention.failure next two flag chores w h) ≤ 1 - ENNReal.ofReal p := by
    rw [hswap]
    exact hbound
  have hfinite : 1 - ENNReal.ofReal p ≠ ∞ := ne_top_of_le_ne_top (by simp) tsub_le_self
  have hreal := ENNReal.toReal_mono hfinite hbound'
  have hpENN : ENNReal.ofReal p ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1
  simpa only [Measure.real, ENNReal.toReal_sub_of_le hpENN (by simp : (1 : ℝ≥0∞) ≠ ∞),
    ENNReal.toReal_one, ENNReal.toReal_ofReal hp0] using hreal

noncomputable def realRate (two : Bool) (n : ℕ) (w : ℝ) : ℝ := (if two then 4 else 2)*w/n
noncomputable def realFactor (two : Bool) (n : ℕ) : ℝ := if two then 1 else 1-1/(n:ℝ)

theorem factor_toReal (two : Bool) (hn : 0 < n) :
    (MoatExperiment.factor two n).toReal = realFactor two n := by
  have hn1 : (1:ℝ≥0∞) ≤ n := by exact_mod_cast hn
  cases two
  · rw [MoatExperiment.factor, if_neg Bool.false_ne_true,
      ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hn1) (by simp)]
    simp [realFactor, one_div]
  · simp [MoatExperiment.factor, realFactor]

theorem actual_detection_real (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 0 < n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (two flag : Bool) (fuel : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hfinite : expectedCost μ next flag ≠ ∞) :
    (μ.prod (MoatDetection.law n)).real (detected next two flag w fuel) ≤
      realRate two n w * ((expectedCost μ next flag).toReal +
        (1-μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)})) := by
  have hrs := (measurable_baselineRequests uniform uniformOracle_measurable).comp
    (baseline_measurable next hnext flag fuel)
  have hdet := MoatTranscript.integrated_detection_le μ hn two w hw hw1
    (fun t => baselineRequests uniform (baseline next flag fuel t)) hrs
  have hbound := hdet.trans (mul_le_mul_right
    (determining_count_integral_le μ next uniform flag hnext (uniformFlagged_measurable flag)
      fuel {A | UniformEF A} measurable_uniformEF) _)
  let S : Set Tape := {t | Successful {A | UniformEF A} (baseline next flag fuel t)}
  have hsub : 1-μ S ≠ ∞ := ne_top_of_le_ne_top (by simp) tsub_le_self
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hrfinite : MoatTranscript.rate two n w ≠ ∞ := by
    cases two <;> simp only [MoatTranscript.rate, Bool.false_eq_true, ite_false, ite_true,
      div_eq_mul_inv]
    all_goals
      apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
      · exact ENNReal.inv_ne_top.mpr hn0
  have hright : MoatTranscript.rate two n w * (expectedCost μ next flag + (1-μ S)) ≠ ∞ :=
    ENNReal.mul_ne_top hrfinite (ENNReal.add_ne_top.mpr ⟨hfinite,hsub⟩)
  have hreal := ENNReal.toReal_mono hright hbound
  have hSle : μ S ≤ 1 := by
    calc
      μ S ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hSreal : (1-μ S).toReal = 1-(μ S).toReal := by
    rw [ENNReal.toReal_sub_of_le hSle (by simp), ENNReal.toReal_one]
  have hrate : (MoatTranscript.rate two n w).toReal = realRate two n w := by
    cases two <;> simp [MoatTranscript.rate, realRate, ENNReal.toReal_ofReal hw]
  simpa only [Measure.real, detected, S, ENNReal.toReal_mul, ENNReal.toReal_add hfinite hsub,
    hrate, hSreal] using hreal

theorem capped_retention (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (two flag chores : Bool) (fuel : ℕ) (w h p : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 < h) (hhw : h ≤ w) (hwidth : 1/(n:ℝ) < w) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfinite : expectedCost μ next flag ≠ ∞)
    (hfixed : ∀ z : MoatSelection.Input n, ENNReal.ofReal p ≤
      μ (eventualSuccess next (MoatExperiment.oracle two flag chores w h z) []
        {A | Fair chores (MoatExperiment.rows two chores w h z) A})) :
    p ≤ (1-realFactor two n)*μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)} +
      realRate two n w * ((expectedCost μ next flag).toReal +
        (1-μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)})) +
      (μ.prod (MoatDetection.law n)).real (geometricLoss next flag fuel h) +
      (μ.prod (MoatDetection.law n)).real (capLoss next flag fuel) := by
  letI : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := by omega
  let := MoatDetection.law_probability n hn0
  let ρ := μ.prod (MoatDetection.law n)
  have hS : MeasurableSet (success next flag fuel) :=
    (measurable_successful _ measurable_uniformEF).preimage
      ((baseline_measurable next hnext flag fuel).comp measurable_fst)
  have hD := MoatExperiment.measurable_decoded (baseline next flag fuel)
    (baseline_measurable next hnext flag fuel) two
  have hretained := retained_failure_mass (μ := ρ) hS hD
    (MoatExperiment.decoded_subset_success (baseline next flag fuel) two)
    (retained_event_inclusion hn next two flag chores fuel w h hw hw1 hh hhw hwidth)
  have hSmeasure : ρ (success next flag fuel) =
      μ {t | Successful {A | UniformEF A} (baseline next flag fuel t)} :=
    by simpa only [ρ, success, Set.preimage_setOf_eq] using
      NonnegativeMainEvents.fst_lift_mass μ (MoatDetection.law n)
        {t | Successful {A | UniformEF A} (baseline next flag fuel t)}
  have hSreal := congrArg ENNReal.toReal hSmeasure
  have hdecode := MoatExperiment.integrated_decoder μ hn0 (baseline next flag fuel)
    (baseline_measurable next hnext flag fuel) two
  have hdecodereal := ENNReal.toReal_mono (measure_ne_top _ _) hdecode
  rw [ENNReal.toReal_mul, factor_toReal two hn0] at hdecodereal
  have hdetect := actual_detection_real μ hn0 next hnext two flag fuel w hw.le hw1 hfinite
  have hfail := actual_failure_real_le μ hn0 w hw next hnext two flag chores h p hh.le hhw hp0 hp1 hfixed
  have hloss : ρ.real (detected next two flag w fuel ∪
      (geometricLoss next flag fuel h ∪ capLoss next flag fuel)) ≤
      ρ.real (detected next two flag w fuel) + ρ.real (geometricLoss next flag fuel h) +
        ρ.real (capLoss next flag fuel) := by
    have houter := measureReal_union_le (μ := ρ) (detected next two flag w fuel)
      (geometricLoss next flag fuel h ∪ capLoss next flag fuel)
    have hinner := measureReal_union_le (μ := ρ) (geometricLoss next flag fuel h) (capLoss next flag fuel)
    linarith
  change ρ.real (success next flag fuel) =
    μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)} at hSreal
  change realFactor two n * μ.real {t | Successful {A | UniformEF A} (baseline next flag fuel t)} ≤
    ρ.real (MoatExperiment.decoded (baseline next flag fuel) two) at hdecodereal
  rw [hSreal] at hretained
  dsimp only [ρ] at hretained hloss hdecodereal
  linarith

end EnvyFreeResearch.Full.MoatCapped
