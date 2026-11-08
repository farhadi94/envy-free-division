import EnvyFreeResearch.Full.NonnegativeCostLedger
import EnvyFreeResearch.Full.NonnegativeDecoderLedger

namespace EnvyFreeResearch.Full.NonnegativeRealLedger

open MeasureTheory Set IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeDetection NonnegativeSuccess
open NonnegativeCostLedger NonnegativeDecoderLedger NonnegativeRandomOutput
open scoped Classical ENNReal

theorem decoderFactor_le_factor_toReal {n : ℕ} (hn : 0 < n) (w : ℝ) (hw : 0 < w) :
    R8Lower.decoderFactor n w ≤ (factor n w).toReal := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hn1 : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (1 - (n : ℝ≥0∞)⁻¹).toReal = 1 - 1 / (n : ℝ) := by
    rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hn1) (by simp)]
    simp [one_div]
  have hbfinite : (ENNReal.ofReal (2 * w))⁻¹ * (n : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity)) (ENNReal.inv_ne_top.mpr hn0)
  have hb := ENNReal.le_toReal_sub (a := 1) hbfinite
  have hbeq : ((ENNReal.ofReal (2 * w))⁻¹ * (n : ℝ≥0∞)⁻¹).toReal = 1 / (2 * (n : ℝ) * w) := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * w), ENNReal.toReal_natCast]
    simp [one_div, mul_inv_rev, mul_comm, mul_left_comm]
  rw [hbeq, ENNReal.toReal_one] at hb
  have hapos : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnr).mpr hnr1
    simpa only [one_div] using sub_nonneg.mpr hi
  rw [factor, ENNReal.toReal_mul, ha]
  exact mul_le_mul_of_nonneg_left hb hapos

theorem integrated_physical_decoder_real {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    (execution : Tape → Execution (Query (Fin n)) Reply (Allocation (Fin n)))
    (hexecution : Measurable execution) (chores : Bool) :
    μ.real {tape | Successful {A | UniformEF A} (execution tape)} * R8Lower.decoderFactor n w ≤
      (μ.prod (perturbLaw n w)).real (decoded execution chores) := by
  let := perturbLaw_probability n hn w hw
  have hENN := integrated_physical_decoder μ hn w hw hwsmall execution hexecution chores
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hENN
  calc
    _ ≤ μ.real {tape | Successful {A | UniformEF A} (execution tape)} * (factor n w).toReal :=
      mul_le_mul_of_nonneg_left (decoderFactor_le_factor_toReal hn w hw) measureReal_nonneg
    _ ≤ _ := by simpa only [Measure.real, ENNReal.toReal_mul, mul_comm] using hreal

theorem actual_capped_detection_real_le {n : ℕ} {Tape Output : Type*}
    [MeasurableSpace Tape] [MeasurableSpace Output]
    (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply Output) (P : Profile (Fin n)) (flag : Bool)
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (horacle : Measurable (IntervalOracle.oracle P))
    (hflagged : Measurable (flaggedOracle flag P)) (fuel : ℕ)
    (good : Set Output) (hgood : MeasurableSet good)
    (hfinite : (∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) ∂μ) ≠ ∞) :
    (μ.prod (perturbLaw n w)).real {z | z.2 ∈ detection
      (baselineRequests P (run next (flaggedOracle flag P) z.1 fuel []))} ≤
      (w / (n : ℝ)) *
        ((∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) ∂μ).toReal +
          (1 - μ.real {tape | Successful good (run next (flaggedOracle flag P) tape fuel [])})) := by
  let S : Set Tape := {tape | Successful good (run next (flaggedOracle flag P) tape fuel [])}
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hsub : 1 - μ S ≠ ∞ := ne_top_of_le_ne_top (by simp) tsub_le_self
  have hrate : ENNReal.ofReal w / (n : ℝ≥0∞) ≠ ∞ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hn0)
  have hbound := actual_capped_detection_le μ hn w hw next P flag hnext horacle hflagged fuel good hgood
  have hright : (ENNReal.ofReal w / (n : ℝ≥0∞)) *
      ((∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) ∂μ) + (1 - μ S)) ≠ ∞ :=
    ENNReal.mul_ne_top hrate (ENNReal.add_ne_top.mpr ⟨hfinite, hsub⟩)
  have hreal := ENNReal.toReal_mono hright hbound
  have hSle : μ S ≤ 1 := calc
    μ S ≤ μ Set.univ := measure_mono (Set.subset_univ S)
    _ = 1 := measure_univ
  have hSreal : (1 - μ S).toReal = 1 - (μ S).toReal := by
    rw [ENNReal.toReal_sub_of_le hSle (by simp : (1 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_one]
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hw.le, ENNReal.toReal_natCast, ENNReal.toReal_add hfinite hsub,
    hSreal] using hreal

end EnvyFreeResearch.Full.NonnegativeRealLedger

#print axioms EnvyFreeResearch.Full.NonnegativeRealLedger.integrated_physical_decoder_real
#print axioms EnvyFreeResearch.Full.NonnegativeRealLedger.actual_capped_detection_real_le
