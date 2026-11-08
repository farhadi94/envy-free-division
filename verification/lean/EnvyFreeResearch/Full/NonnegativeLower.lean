import EnvyFreeResearch.Full.NonnegativeHardFamily

namespace EnvyFreeResearch.Full.NonnegativeLower

open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeExperiment
open NonnegativeRandomOutput NonnegativeRetainedFailure NonnegativeEndpointCapture
open NonnegativeDetection NonnegativeProbability NonnegativeMainEvents NonnegativeHardFamily Filter
open scoped Classical ENNReal Topology

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

theorem small_geometric_loss (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (fuel : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      (μ.prod (perturbLaw n w)).real (geometricLoss next flag fuel h) < ε := by
  let width : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hwidth : ∀ m, 0 < width m := by intro m; dsimp only [width]; positivity
  have hmono : Antitone width := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1)
    exact add_le_add (by exact_mod_cast hij) le_rfl
  have hlim : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨m, hm0, hm1, hsmall⟩ := exists_actual_width μ hn w hw uniform uniformOracle_measurable
    (baseline next flag fuel) (baseline_measurable next hnext flag fuel)
    width hwidth hmono hlim (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨width m, hm0, hm1, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal
    ((geometricLoss_mass_le μ hn w hw next flag fuel (width m)).trans_lt hsmall)

theorem small_cap_loss (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (hfinite : expectedCost μ next flag ≠ ∞) (ε : ℝ) (hε : 0 < ε) :
    ∃ fuel : ℕ, (μ.prod (perturbLaw n w)).real (capLoss next flag fuel) < ε := by
  let := perturbLaw_probability n hn w hw
  have hlim := exhaustion_tendsto_zero μ next (flaggedOracle flag uniform) hnext
    (uniformFlagged_measurable flag) [] hfinite
  obtain ⟨fuel, hfuel⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨fuel, ?_⟩
  have heq : (μ.prod (perturbLaw n w)) (capLoss next flag fuel) =
      μ {tape | Exhausted (baseline next flag fuel tape)} :=
    fst_lift_mass μ (perturbLaw n w) {tape | Exhausted (baseline next flag fuel tape)}
  change ((μ.prod (perturbLaw n w)) (capLoss next flag fuel)).toReal < ε
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hfuel

/-- End-to-end lower bound for the explicit normalized bounded pulse family.
The hypothesis is only fixed-input correctness of the actual adaptive
protocol. All randomness, endpoint capture, replay, old failures, decoding,
illegal-call accounting and unconditional expectation are proved above.
The universal public input-class theorem specializes its guarantee to this
explicit family. -/
theorem all_windows (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfixed : ∀ h : ℝ, 0 < h → h < 1 → ∀ input : Input n,
      ENNReal.ofReal p ≤ μ (eventualSuccess next (inputOracle flag h input) []
        {A | Fair chores (inputRows h input) A}))
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    ENNReal.ofReal (R8Lower.retainedQueryLower n p w) ≤ expectedCost μ next flag := by
  letI : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  by_cases hfinite : expectedCost μ next flag ≠ ∞
  · have hreal : R8Lower.retainedQueryLower n p w ≤ (expectedCost μ next flag).toReal := by
      apply le_of_forall_pos_le_add
      intro ε hε
      let δ : ℝ := ε * w / (2 * (n : ℝ))
      have hδ : 0 < δ := by dsimp only [δ]; positivity
      obtain ⟨fuel, hcap⟩ := small_cap_loss μ hn0 w hw next hnext flag hfinite δ hδ
      obtain ⟨h, hh0, hh1, hgeometry⟩ := small_geometric_loss μ hn0 w hw next hnext flag fuel δ hδ
      have hbound := capped_retained_lower μ hn w hw hwsmall next hnext flag chores fuel h p
        hh0 hp0 hp1 hfinite (hfixed h hh0 hh1)
      have hscale : 0 < (n : ℝ) / w := div_pos hnr hw
      have herror : ((n : ℝ) / w) *
          ((μ.prod (perturbLaw n w)).real (geometricLoss next flag fuel h) +
            (μ.prod (perturbLaw n w)).real (capLoss next flag fuel)) < ε := by
        calc
          _ < ((n : ℝ) / w) * (2 * δ) := mul_lt_mul_of_pos_left (by linarith) hscale
          _ = ε := by dsimp only [δ]; field_simp
      have hid : R8Lower.retainedQueryLower n p w =
          R8Lower.retainedQueryLower n
            (p - (μ.prod (perturbLaw n w)).real (geometricLoss next flag fuel h) -
              (μ.prod (perturbLaw n w)).real (capLoss next flag fuel)) w +
          ((n : ℝ) / w) *
            ((μ.prod (perturbLaw n w)).real (geometricLoss next flag fuel h) +
              (μ.prod (perturbLaw n w)).real (capLoss next flag fuel)) := by
        unfold R8Lower.retainedQueryLower
        ring
      rw [hid]
      linarith
    calc
      ENNReal.ofReal (R8Lower.retainedQueryLower n p w) ≤
          ENNReal.ofReal (expectedCost μ next flag).toReal := ENNReal.ofReal_le_ofReal hreal
      _ = expectedCost μ next flag := ENNReal.ofReal_toReal hfinite
  · simp [not_ne_iff.mp hfinite]

/-- The manuscript's optimized explicit constant, still stated for the
literal physical hard family so its admission into any public input class
can be checked separately and then specialized without further probability
or oracle hypotheses. -/
theorem optimized (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfixed : ∀ h : ℝ, 0 < h → h < 1 → ∀ input : Input n,
      ENNReal.ofReal p ≤ μ (eventualSuccess next (inputOracle flag h input) []
        {A | Fair chores (inputRows h input) A}))
    (hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p) :
    ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1))) ≤
      expectedCost μ next flag := by
  have hnr2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hnr1 : (1 : ℝ) < n := by linarith
  have hmul := mul_le_mul_of_nonneg_left hthreshold hnr.le
  have hdiv : (n : ℝ) * (3 - 2 / (n : ℝ)) = 3 * n - 2 := by field_simp
  rw [hdiv] at hmul
  have hlegal : 2 * ((n : ℝ) - 1) ≤ (n : ℝ) * ((n : ℝ) * p - 1) := by nlinarith
  have hnp : 1 < (n : ℝ) * p := by nlinarith
  obtain ⟨hw, hwsmall⟩ := R8Lower.retained_window_legal n p hnr1 hnp hlegal
  have hbound := all_windows μ hn next hnext flag chores p hp0 hp1 hfixed
    (R8Lower.retainedWindow n p) hw hwsmall
  simpa only [R8Lower.retained_optimized_value n p hnr1 hnp, R8Lower.retainedConstant] using hbound

end EnvyFreeResearch.Full.NonnegativeLower

#print axioms EnvyFreeResearch.Full.NonnegativeLower.all_windows
#print axioms EnvyFreeResearch.Full.NonnegativeLower.optimized
