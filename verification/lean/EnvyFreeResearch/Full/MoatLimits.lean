import EnvyFreeResearch.Full.MoatRetention
import EnvyFreeResearch.Full.NonnegativeHardFamily

namespace EnvyFreeResearch.Full.MoatLimits
open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable Filter
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRandomOutput
open NonnegativeRetainedFailure NonnegativeEndpointCapture NonnegativeProbability
open NonnegativeMeasurableDetection NonnegativeExperiment NonnegativeHardFamily
open MoatSelection MoatRetention
open scoped Classical ENNReal Topology

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

theorem geometricLoss_mass_le (μ : Measure Tape) (hn : 0 < n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) (h : ℝ) :
    (μ.prod (MoatDetection.law n)) (geometricLoss next flag fuel h) ≤
      (μ.prod (MoatDetection.law n)) (endpointHit
        (fun t => endpointCount uniform (baseline next flag fuel t))
        (fun t k => endpoint uniform (baseline next flag fuel t) k) center h) +
      μ (NonnegativeMainEvents.gapLoss next flag fuel h) := by
  let := MoatDetection.law_probability n hn
  have h := measure_union_le (μ := μ.prod (MoatDetection.law n))
    (endpointHit (fun t => endpointCount uniform (baseline next flag fuel t))
      (fun t k => endpoint uniform (baseline next flag fuel t) k) center h)
    (Prod.fst ⁻¹' NonnegativeMainEvents.gapLoss next flag fuel h)
  rw [NonnegativeMainEvents.fst_lift_mass μ (MoatDetection.law n)] at h
  exact h

theorem small_geometric_loss (μ : Measure Tape) [IsProbabilityMeasure μ]
    (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (fuel : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ w ∧
      (μ.prod (MoatDetection.law n)).real (geometricLoss next flag fuel h) < ε := by
  let := MoatDetection.law_probability n hn
  let width : ℕ → ℝ := fun m => w/((m:ℝ)+1)
  have hwidth : ∀ m, 0 < width m := by intro m; dsimp only [width]; positivity
  have hwidthle : ∀ m, width m ≤ w := by
    intro m
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hmono : Antitone width := by
    intro i j hij
    exact div_le_div_of_nonneg_left hw.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hlim : Tendsto width atTop (𝓝 0) := by
    have hz : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [width, mul_zero, div_eq_mul_inv, one_mul] using hz.const_mul w
  obtain ⟨m,hm0,_,hsmall⟩ := NonnegativeProbability.exists_one_width
    (μ := μ) (ν := MoatDetection.law n)
    (fun t => endpointCount uniform (baseline next flag fuel t))
    (fun t k => endpoint uniform (baseline next flag fuel t) k) center center
    ((measurable_endpointCount uniform uniformOracle_measurable).comp
      (baseline_measurable next hnext flag fuel))
    (fun k => (measurable_endpoint uniform uniformOracle_measurable k).comp
      (baseline_measurable next hnext flag fuel))
    center_measurable center_measurable center_atomless center_atomless
    ((measurable_successful _ measurable_uniformEF.compl).preimage
      (baseline_measurable next hnext flag fuel))
    (fun t => outputGap (baseline next flag fuel t))
    (measurable_outputGap.comp (baseline_measurable next hnext flag fuel))
    (fun t ht => outputGap_positive _ ht)
    width hwidth hmono hlim (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨width m,hm0,hwidthle m,?_⟩
  apply ENNReal.toReal_lt_of_lt_ofReal
  apply (geometricLoss_mass_le μ hn next flag fuel (width m)).trans_lt
  apply lt_of_le_of_lt _ hsmall
  change _ + μ (NonnegativeMainEvents.gapLoss next flag fuel (width m)) ≤
    _ + _ + μ (NonnegativeMainEvents.gapLoss next flag fuel (width m))
  exact add_le_add (le_add_right le_rfl) le_rfl

theorem small_cap_loss (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 0 < n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (hfinite : expectedCost μ next flag ≠ ∞) (ε : ℝ) (hε : 0 < ε) :
    ∃ fuel : ℕ, (μ.prod (MoatDetection.law n)).real (capLoss next flag fuel) < ε := by
  let := MoatDetection.law_probability n hn
  have hlim := exhaustion_tendsto_zero μ next (flaggedOracle flag uniform) hnext
    (uniformFlagged_measurable flag) [] hfinite
  obtain ⟨fuel,hfuel⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨fuel,?_⟩
  have heq : (μ.prod (MoatDetection.law n)) (capLoss next flag fuel) =
      μ {t | Exhausted (baseline next flag fuel t)} :=
    by simpa only [capLoss, Set.preimage_setOf_eq] using
      NonnegativeMainEvents.fst_lift_mass μ (MoatDetection.law n)
        {t | Exhausted (baseline next flag fuel t)}
  change ((μ.prod (MoatDetection.law n)) (capLoss next flag fuel)).toReal < ε
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hfuel

end EnvyFreeResearch.Full.MoatLimits
