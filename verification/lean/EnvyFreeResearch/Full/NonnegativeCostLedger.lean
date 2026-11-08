import EnvyFreeResearch.Full.NonnegativeMeasurableDetection
import EnvyFreeResearch.Full.NonnegativeSuccess

namespace EnvyFreeResearch.Full.NonnegativeCostLedger

open Set MeasureTheory IntervalOracle OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeDetection
open NonnegativeMeasurableDetection NonnegativeSuccess
open scoped Classical ENNReal

variable {n : ℕ} {Tape Output : Type*} [MeasurableSpace Tape] [MeasurableSpace Output]

theorem illegalIndicator_le_one {Q R O : Type*} (e : Execution Q R O) : illegalIndicator e ≤ 1 := by
  cases he : e.stop <;> simp [illegalIndicator, he]

/-- The determining-list charge is the unconditional answered count plus at
most the failure indicator. Successful outputs never pay the uncounted
illegal-request correction. This is the sharp correction in the paper. -/
theorem determining_count_integral_le
    (μ : Measure Tape) [IsProbabilityMeasure μ]
    (next : Protocol Tape (Query (Fin n)) Reply Output) (P : Profile (Fin n)) (flag : Bool)
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (hflagged : Measurable (flaggedOracle flag P)) (fuel : ℕ)
    (good : Set Output) (hgood : MeasurableSet good) :
    (∫⁻ tape, ((baselineRequests P (run next (flaggedOracle flag P) tape fuel [])).length : ℝ≥0∞) ∂μ) ≤
      (∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) ∂μ) +
        (1 - μ {tape | Successful good (run next (flaggedOracle flag P) tape fuel [])}) := by
  let S : Set Tape := {tape | Successful good (run next (flaggedOracle flag P) tape fuel [])}
  have hS : MeasurableSet S := measurable_cap_success next (flaggedOracle flag P)
    hnext hflagged [] good hgood fuel
  have hQ : Measurable (fun tape => (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞)) :=
    (measurable_of_countable (fun q : ℕ∞ => (q : ℝ≥0∞))).comp
      (measurable_queryCost next (flaggedOracle flag P) hnext hflagged [])
  have hpoint (tape : Tape) :
      ((baselineRequests P (run next (flaggedOracle flag P) tape fuel [])).length : ℝ≥0∞) ≤
        (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) + Sᶜ.indicator (fun _ => 1) tape := by
    have hcost : ((run next (flaggedOracle flag P) tape fuel []).answered.length : ℝ≥0∞) ≤
        (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) := by
      exact_mod_cast ENat.toENNReal_mono
        (le_iSup (fun k : ℕ => ((run next (flaggedOracle flag P) tape k []).answered.length : ℕ∞)) fuel)
    have hj : (illegalIndicator (run next (flaggedOracle flag P) tape fuel []) : ℝ≥0∞) ≤
        Sᶜ.indicator (fun _ => 1) tape := by
      by_cases hs : tape ∈ S
      · obtain ⟨output, hreturned, _⟩ := hs
        have hillegal0 : illegalIndicator (run next (flaggedOracle flag P) tape fuel []) = 0 := by
          simp [illegalIndicator, hreturned]
        rw [hillegal0, Nat.cast_zero]
        exact bot_le
      · rw [indicator_of_mem (show tape ∈ Sᶜ from hs)]
        exact_mod_cast illegalIndicator_le_one (run next (flaggedOracle flag P) tape fuel [])
    rw [baselineRequests_length, Nat.cast_add]
    exact add_le_add hcost hj
  calc
    _ ≤ ∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) +
        Sᶜ.indicator (fun _ => 1) tape ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left hQ, lintegral_indicator_const hS.compl 1, one_mul,
        measure_compl hS (measure_ne_top _ _), measure_univ]

/-- Sharp detection cost for the actual adaptive capped transcript. The
proof derives its joint event measurability and its determining-interval
count from the execution; no detection bound is an interface premise. -/
theorem actual_capped_detection_le (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply Output) (P : Profile (Fin n)) (flag : Bool)
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (horacle : Measurable (IntervalOracle.oracle P))
    (hflagged : Measurable (flaggedOracle flag P)) (fuel : ℕ)
    (good : Set Output) (hgood : MeasurableSet good) :
    (μ.prod (perturbLaw n w)) {z | z.2 ∈ detection
      (baselineRequests P (run next (flaggedOracle flag P) z.1 fuel []))} ≤
      (ENNReal.ofReal w / (n : ℝ≥0∞)) *
        ((∫⁻ tape, (queryCost next (flaggedOracle flag P) tape [] : ℝ≥0∞) ∂μ) +
          (1 - μ {tape | Successful good (run next (flaggedOracle flag P) tape fuel [])})) := by
  have hrequests := (measurable_baselineRequests P horacle).comp
    (measurable_run_at_history next (flaggedOracle flag P) hnext hflagged fuel [])
  have hdetect := integrated_detection_le μ hn w hw
    (fun tape => baselineRequests P (run next (flaggedOracle flag P) tape fuel []))
    (actual_detection_measurable next P flag hnext horacle hflagged fuel)
    (measurable_list_length.comp hrequests)
  exact hdetect.trans (mul_le_mul_right
    (determining_count_integral_le μ next P flag hnext hflagged fuel good hgood) _)

end EnvyFreeResearch.Full.NonnegativeCostLedger

#print axioms EnvyFreeResearch.Full.NonnegativeCostLedger.determining_count_integral_le
#print axioms EnvyFreeResearch.Full.NonnegativeCostLedger.actual_capped_detection_le
