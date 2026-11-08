import EnvyFreeResearch.Full.UpperFreshSamples
import Mathlib.Probability.UniformOn

/-!
# Ordinary-query mixture sampling with the full iid law

Choose an actual active agent uniformly and execute its normalized recorded
union sampler. Sequential calls expose their entire answered histories to
the legal reply policy. The sample vector nonetheless has the exact iid
mixture law, proved from the concrete executor rather than postulated.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval BigOperators Classical

namespace EnvyFreeResearch.Full.UpperMixtureSampling

open UpperCircularStage UpperRecordedDomain UpperUnionSampling UpperUnionMeasurable
  UpperStageMeasurable UpperAdaptiveProduct Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

def seedLaw (Agent : Type*) [Fintype Agent] [MeasurableSpace Agent] : Measure (Agent × I) :=
  (uniformOn Set.univ).prod volume

instance seedLaw_probability [Nonempty Agent] : IsProbabilityMeasure (seedLaw Agent) := by
  unfold seedLaw
  infer_instance

def mixture (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (cells : List Component) : Measure ℝ :=
  (Fintype.card Agent : ℝ≥0∞)⁻¹ • ∑ a, cond (μ (active a)) (domain cells)

def sample (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (history : History n) (draw : Agent × I) : ℝ × History n :=
  sampleExecution policy history (active draw.1) (cached draw.1)
    ((μ (active draw.1)).real (domain cells)) cells draw.2

theorem sample_measurable (μ : Fin n → Measure ℝ) (policy : Policy n)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) :
    Measurable (Function.uncurry (sample μ policy active cached cells)) := by
  have h : Measurable (fun p : Agent × (History n × I) =>
      sampleExecution policy p.2.1 (active p.1) (cached p.1)
        ((μ (active p.1)).real (domain cells)) cells p.2.2) := by
    apply measurable_from_prod_countable_right
    intro a
    exact sampleExecution_family_measurable policy hmeas Prod.fst measurable_fst
      (active a) (cached a) ((μ (active a)).real (domain cells)) cells Prod.snd measurable_snd
  exact h.comp (((measurable_fst.comp measurable_snd)).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

omit [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem sample_query_bound (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (history : History n) (draw : Agent × I) :
    (sample μ policy active cached cells history draw).2.length ≤ history.length + (n + 1) := by
  exact (sampleExecution_query_bound policy history (active draw.1) (cached draw.1)
    ((μ (active draw.1)).real (domain cells)) cells draw.2).trans_eq (by omega)

omit [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem sample_cut_bound (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (history : History n) (draw : Agent × I) :
    ((sample μ policy active cached cells history draw).2.map Prod.fst).countP isCut ≤
      (history.map Prod.fst).countP isCut + 1 :=
  sampleExecution_cut_bound policy history (active draw.1) (cached draw.1)
    ((μ (active draw.1)).real (domain cells)) cells draw.2

/-- The one-call law is the explicit equally weighted normalized mixture. -/
theorem sample_law (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
    (hcache : ∀ a c, c ∈ cells → cached a c = mass (μ (active a)) c)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells)) (history : History n) :
    (seedLaw Agent).map (fun draw => (sample μ policy active cached cells history draw).1) =
      mixture μ active cells := by
  have hsamp : Measurable (fun draw => sample μ policy active cached cells history draw) :=
    (sample_measurable μ policy hmeas active cached cells).comp
      (measurable_const.prodMk measurable_id)
  have hfirst : Measurable (fun draw => (sample μ policy active cached cells history draw).1) :=
    measurable_fst.comp hsamp
  have hunif : (uniformOn Set.univ : Measure Agent) = (Fintype.card Agent : ℝ≥0∞)⁻¹ • Measure.count := by
    ext s hs
    simp only [uniformOn_univ, Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hfirst hS, seedLaw, Measure.prod_apply (hS.preimage hfirst)]
  have hone (a : Agent) : Measurable (fun draw => (sampleExecution policy history (active a)
      (cached a) ((μ (active a)).real (domain cells)) cells draw).1) :=
    measurable_fst.comp (sampleExecution_measurable policy hmeas history (active a) (cached a) _ cells)
  have hfiber (a : Agent) :
      (volume : Measure I) ((fun draw => (a, draw)) ⁻¹'
        ((fun draw => (sample μ policy active cached cells history draw).1) ⁻¹' S)) =
          cond (μ (active a)) (domain cells) S := by
    rw [← sampleExecution_law μ policy hpolicy history (active a) (cached a) cells
      hordered hdisjoint (hcache a) (hpositive a) (hone a), Measure.map_apply (hone a) hS]
    rfl
  simp_rw [hfiber]
  rw [hunif, lintegral_smul_measure, lintegral_count, tsum_fintype]
  simp only [mixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

/-- All sample coordinates are iid even though each later Cut reply can
depend on every query and answer made during the earlier samples. -/
theorem iid_sample_law [Nonempty Agent] (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
    (hcache : ∀ a c, c ∈ cells → cached a c = mass (μ (active a)) c)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells))
    (m : ℕ) (history : History n) :
    MeasurePreserving (fun draw => (UpperFreshSamples.run
      (sample μ policy active cached cells) m history draw).1)
      (tapeLaw (seedLaw Agent) m) (tapeLaw (mixture μ active cells) m) := by
  have hlaw := sample_law μ policy hpolicy hmeas active cached cells hordered hdisjoint hcache hpositive
  let : IsProbabilityMeasure (mixture μ active cells) := by
    rw [← hlaw history]
    infer_instance
  exact UpperFreshSamples.independent_samples (sample μ policy active cached cells)
    (sample_measurable μ policy hmeas active cached cells) (seedLaw Agent) (mixture μ active cells)
    hlaw m history

omit [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
/-- The deterministic all-draw cost includes every original observer's
recording after every actual Cut. -/
theorem samples_query_bound (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (m : ℕ) (history : History n) (draw : Fin m → Agent × I) :
    (UpperFreshSamples.run (sample μ policy active cached cells) m history draw).2.length ≤
      history.length + m * (n + 1) :=
  UpperFreshSamples.cost_bound (sample μ policy active cached cells) List.length (n + 1)
    (sample_query_bound μ policy active cached cells) m history draw

omit [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem samples_cut_bound (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component)
    (m : ℕ) (history : History n) (draw : Fin m → Agent × I) :
    ((UpperFreshSamples.run (sample μ policy active cached cells) m history draw).2.map Prod.fst).countP isCut ≤
      (history.map Prod.fst).countP isCut + m := by
  simpa only [mul_one] using UpperFreshSamples.cost_bound (sample μ policy active cached cells)
    (fun h => (h.map Prod.fst).countP isCut) 1 (sample_cut_bound μ policy active cached cells) m history draw

end EnvyFreeResearch.Full.UpperMixtureSampling
