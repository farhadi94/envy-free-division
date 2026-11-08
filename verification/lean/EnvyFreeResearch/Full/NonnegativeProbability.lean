import Mathlib
import EnvyFreeResearch.R8Lower

/-!
# Probability steps for the nonnegative lower bound

All sample spaces here are arbitrary measurable spaces. In particular, none
of these results substitutes finite-support random tapes for ideal-real
randomness. The endpoint theorem uses the actual random endpoint coordinates
and their finite (possibly nonintegrable) count. It does not assume a bound on
the desired endpoint-loss probability.
-/

namespace EnvyFreeResearch.Full.NonnegativeProbability

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
variable {μ : Measure Ω} {ν : Measure Θ}

/-- Tonelli averages guarantees for fixed independently sampled inputs. The
set may encode any jointly measurable failure predicate; no regular
conditional distribution on the random tape space is required. -/
theorem fixed_input_average [IsProbabilityMeasure ν] [SFinite μ]
    {failure : Set (Θ × Ω)} (hfailure : MeasurableSet failure) {b : ℝ≥0∞}
    (hfixed : ∀ input, μ {tape | (input, tape) ∈ failure} ≤ b) :
    (ν.prod μ) failure ≤ b := by
  rw [Measure.prod_apply hfailure]
  calc
    (∫⁻ input, μ (Prod.mk input ⁻¹' failure) ∂ν) ≤ ∫⁻ _input, b ∂ν :=
      lintegral_mono hfixed
    _ = b := by simp

/-- A direct real-probability retention inequality for actual measurable
events, extending the original finite weighted certificate. -/
theorem retained_failure_mass [IsProbabilityMeasure μ]
    {success decoded loss failure : Set Ω}
    (hsuccess : MeasurableSet success) (hdecoded : MeasurableSet decoded)
    (hsub : decoded ⊆ success)
    (hpersist : (successᶜ ∪ decoded) \ loss ⊆ failure) :
    1 - μ.real success + μ.real decoded - μ.real loss ≤ μ.real failure := by
  have hdisjoint : Disjoint successᶜ decoded := by
    refine Set.disjoint_left.mpr ?_
    intro tape hs hd
    exact hs (hsub hd)
  have hmass : μ.real (successᶜ ∪ decoded) =
      1 - μ.real success + μ.real decoded := by
    rw [measureReal_union hdisjoint hdecoded, probReal_compl_eq_one_sub hsuccess]
  rw [← hmass]
  exact (le_measureReal_sdiff (μ := μ)).trans (measureReal_mono hpersist)

/-- Measurable random finite endpoint lists, padded by an arbitrary real
coordinate after their finite length. Padding does not enter the event. -/
def endpointHit (count : Ω → ℕ) (endpoint : Ω → ℕ → ℝ)
    (center : Θ → ℝ) (width : ℝ) : Set (Ω × Θ) :=
  {z | ∃ k, k < count z.1 ∧ |center z.2 - endpoint z.1 k| ≤ width}

theorem measurable_endpointHit (count : Ω → ℕ) (endpoint : Ω → ℕ → ℝ)
    (center : Θ → ℝ) (width : ℝ)
    (hcount : Measurable count) (hendpoint : ∀ k, Measurable (fun tape => endpoint tape k))
    (hcenter : Measurable center) :
    MeasurableSet (endpointHit count endpoint center width) := by
  have heq : endpointHit count endpoint center width =
      ⋃ k : ℕ, {z : Ω × Θ | k < count z.1} ∩
        {z : Ω × Θ | |center z.2 - endpoint z.1 k| ≤ width} := by
    ext z
    simp [endpointHit]
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_lt measurable_const (hcount.comp measurable_fst)).inter
    (measurableSet_le (((hcenter.comp measurable_snd).sub
      ((hendpoint k).comp measurable_fst)).abs) measurable_const)

/-- Independent atomless center laws almost surely avoid each measurable
random endpoint, even when the endpoint distribution itself has atoms. -/
theorem random_endpoint_eq_null [SFinite ν]
    (endpoint : Ω → ℝ) (center : Θ → ℝ)
    (hendpoint : Measurable endpoint) (hcenter : Measurable center)
    (hatomless : ∀ a : ℝ, ν {input | center input = a} = 0) :
    (μ.prod ν) {z : Ω × Θ | center z.2 = endpoint z.1} = 0 := by
  have hmeas : MeasurableSet {z : Ω × Θ | center z.2 = endpoint z.1} :=
    measurableSet_eq_fun (hcenter.comp measurable_snd) (hendpoint.comp measurable_fst)
  rw [Measure.prod_apply hmeas]
  have hzero : (fun tape => ν (Prod.mk tape ⁻¹'
      {z : Ω × Θ | center z.2 = endpoint z.1})) = fun _ => 0 := by
    funext tape
    exact hatomless (endpoint tape)
  rw [hzero]
  simp

/-- Shrinking a deterministic width makes the endpoint-hit probability tend
to zero. The random list is merely finite on each tape: no bound or finite
expectation on its length is used. The center is independent of the tape,
and only its atomlessness, not a density estimate, is required. -/
theorem endpoint_loss_tendsto_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (count : Ω → ℕ) (endpoint : Ω → ℕ → ℝ) (center : Θ → ℝ)
    (hcount : Measurable count) (hendpoint : ∀ k, Measurable (fun tape => endpoint tape k))
    (hcenter : Measurable center)
    (hatomless : ∀ a : ℝ, ν {input | center input = a} = 0)
    (width : ℕ → ℝ) (hmono : Antitone width) (hlim : Tendsto width atTop (𝓝 0)) :
    Tendsto (fun m => (μ.prod ν) (endpointHit count endpoint center (width m)))
      atTop (𝓝 0) := by
  let hit := fun m => endpointHit count endpoint center (width m)
  have hmeas : ∀ m, MeasurableSet (hit m) := fun m =>
    measurable_endpointHit count endpoint center (width m) hcount hendpoint hcenter
  have hanti : Antitone hit := by
    intro i j hij z hz
    obtain ⟨k, hk, hdist⟩ := hz
    exact ⟨k, hk, hdist.trans (hmono hij)⟩
  have hsubset : (⋂ m, hit m) ⊆
      ⋃ k : ℕ, {z : Ω × Θ | center z.2 = endpoint z.1 k} := by
    intro z hz
    by_contra hno
    have hne : ∀ k : ℕ, center z.2 ≠ endpoint z.1 k := by
      simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] using hno
    have hsmall : ∀ k ∈ Finset.range (count z.1),
        ∀ᶠ m in atTop, width m < |center z.2 - endpoint z.1 k| := by
      intro k _
      exact hlim.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr (hne k))))
    have hall : ∀ᶠ m in atTop, ∀ k ∈ Finset.range (count z.1),
        width m < |center z.2 - endpoint z.1 k| :=
      (Finset.eventually_all (Finset.range (count z.1))).mpr hsmall
    obtain ⟨m, hm⟩ := hall.exists
    obtain ⟨k, hk, hdist⟩ := Set.mem_iInter.mp hz m
    exact (not_lt_of_ge hdist) (hm k (Finset.mem_range.mpr hk))
  have hnull : (μ.prod ν) (⋂ m, hit m) = 0 := by
    apply measure_mono_null hsubset
    apply measure_iUnion_null
    intro k
    exact random_endpoint_eq_null (fun tape => endpoint tape k) center
      (hendpoint k) hcenter hatomless
  have ht := tendsto_measure_iInter_atTop
    (fun m => (hmeas m).nullMeasurableSet) hanti
    (show ∃ m, (μ.prod ν) (hit m) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  simpa only [Function.comp_def, hnull] using ht

/-- Strictly incorrect old outputs remain separated from exact fairness at
a sufficiently small deterministic width, except on arbitrarily small mass.
No uniform positive lower bound on the gap is assumed. -/
theorem positive_gap_loss_tendsto_zero [IsFiniteMeasure μ]
    {wrong : Set Ω} (hwrong : MeasurableSet wrong) (gap : Ω → ℝ)
    (hgap : Measurable gap) (hpositive : ∀ tape ∈ wrong, 0 < gap tape)
    (width : ℕ → ℝ) (hmono : Antitone width) (hlim : Tendsto width atTop (𝓝 0)) :
    Tendsto (fun m => μ (wrong ∩ {tape | gap tape ≤ width m})) atTop (𝓝 0) := by
  let loss := fun m => wrong ∩ {tape | gap tape ≤ width m}
  have hmeas : ∀ m, MeasurableSet (loss m) := fun m =>
    hwrong.inter (measurableSet_le hgap measurable_const)
  have hanti : Antitone loss := by
    intro i j hij tape ht
    exact ⟨ht.1, ht.2.trans (hmono hij)⟩
  have hempty : (⋂ m, loss m) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro tape ht
    have hw : tape ∈ wrong := (Set.mem_iInter.mp ht 0).1
    have hev := hlim.eventually (gt_mem_nhds (hpositive tape hw))
    obtain ⟨m, hm⟩ := hev.exists
    exact (not_lt_of_ge (Set.mem_iInter.mp ht m).2) hm
  have ht := tendsto_measure_iInter_atTop
    (fun m => (hmeas m).nullMeasurableSet) hanti
    (show ∃ m, μ (loss m) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  simpa only [Function.comp_def, hempty, measure_empty] using ht

/-- One deterministic index simultaneously controls both bump centers and
every strictly unfair old output. The centers may be correlated with each
other; only their law's independence from the tape and their atomless
marginals are used. -/
theorem exists_one_width [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (count : Ω → ℕ) (endpoint : Ω → ℕ → ℝ) (first second : Θ → ℝ)
    (hcount : Measurable count) (hendpoint : ∀ k, Measurable (fun tape => endpoint tape k))
    (hfirst : Measurable first) (hsecond : Measurable second)
    (hfirstAtomless : ∀ a : ℝ, ν {input | first input = a} = 0)
    (hsecondAtomless : ∀ a : ℝ, ν {input | second input = a} = 0)
    {wrong : Set Ω} (hwrong : MeasurableSet wrong) (gap : Ω → ℝ)
    (hgap : Measurable gap) (hpositive : ∀ tape ∈ wrong, 0 < gap tape)
    (width : ℕ → ℝ) (hwidth : ∀ m, 0 < width m)
    (hmono : Antitone width) (hlim : Tendsto width atTop (𝓝 0))
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ m, 0 < width m ∧ width m < 1 ∧
      (μ.prod ν) (endpointHit count endpoint first (width m)) +
      (μ.prod ν) (endpointHit count endpoint second (width m)) +
      μ (wrong ∩ {tape | gap tape ≤ width m}) < η := by
  have hfirstLimit := endpoint_loss_tendsto_zero (μ := μ) (ν := ν) count endpoint first
    hcount hendpoint hfirst hfirstAtomless width hmono hlim
  have hsecondLimit := endpoint_loss_tendsto_zero (μ := μ) (ν := ν) count endpoint second
    hcount hendpoint hsecond hsecondAtomless width hmono hlim
  have hgapLimit := positive_gap_loss_tendsto_zero (μ := μ) hwrong gap hgap hpositive width hmono hlim
  have htotal : Tendsto (fun m =>
      (μ.prod ν) (endpointHit count endpoint first (width m)) +
      (μ.prod ν) (endpointHit count endpoint second (width m)) +
      μ (wrong ∩ {tape | gap tape ≤ width m})) atTop (𝓝 0) := by
    simpa only [add_zero] using (hfirstLimit.add hsecondLimit).add hgapLimit
  have hevent := (htotal.eventually (gt_mem_nhds hη)).and
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)))
  obtain ⟨m, hm⟩ := hevent.exists
  exact ⟨m, hwidth m, hm.2, hm.1⟩

/-- This composes actual event bounds and eliminates arbitrarily small
geometric losses. It is a reusable probability theorem, not the manuscript's
main theorem: callers must still construct and prove the decoder, detection,
and pointwise replay inclusions for the actual oracle and pulse law. -/
theorem query_lower_from_events [IsProbabilityMeasure μ]
    {success decoded detection : Set Ω} (failure loss : ℕ → Set Ω)
    (hsuccess : MeasurableSet success) (hdecoded : MeasurableSet decoded)
    (hsub : decoded ⊆ success)
    (hpersist : ∀ m, (successᶜ ∪ decoded) \ (detection ∪ loss m) ⊆ failure m)
    (n p w q j : ℝ) (hn : 2 ≤ n) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    (hillegal : j ≤ 1 - μ.real success)
    (hdecode : μ.real success * R8Lower.decoderFactor n w ≤ μ.real decoded)
    (hdetect : μ.real detection ≤ (w / n) * (q + j))
    (hfixed : ∀ m, μ.real (failure m) ≤ 1 - p)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ m, μ.real (loss m) < η) :
    R8Lower.retainedQueryLower n p w ≤ q := by
  apply R8Lower.query_lower_from_retention n w (μ.real success) p q j
    hn hw hwsmall (by simpa using measureReal_mono (μ := μ) (Set.subset_univ success)) hillegal
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨m, hm⟩ := hsmall η hη
  have hretained := retained_failure_mass (μ := μ) hsuccess hdecoded hsub (hpersist m)
  have hloss := measureReal_union_le (μ := μ) detection (loss m)
  have hfailure := hfixed m
  linarith

end EnvyFreeResearch.Full.NonnegativeProbability

#print axioms EnvyFreeResearch.Full.NonnegativeProbability.fixed_input_average
#print axioms EnvyFreeResearch.Full.NonnegativeProbability.retained_failure_mass
#print axioms EnvyFreeResearch.Full.NonnegativeProbability.endpoint_loss_tendsto_zero
#print axioms EnvyFreeResearch.Full.NonnegativeProbability.positive_gap_loss_tendsto_zero
#print axioms EnvyFreeResearch.Full.NonnegativeProbability.exists_one_width
#print axioms EnvyFreeResearch.Full.NonnegativeProbability.query_lower_from_events
