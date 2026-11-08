import EnvyFreeResearch.Full.NonnegativeProfile
import EnvyFreeResearch.Full.NonnegativeRandomOutput

namespace EnvyFreeResearch.Full.NonnegativeMeasurablePulse

set_option maxHeartbeats 600000

open MeasureTheory Set Metric IntervalAllocation MixedDensity
open NonnegativePulse NonnegativeOutputMeasurable

abbrev Circle := NonnegativeCircle.Circle
abbrev Centers := Circle × Circle

/-- Joint measurability of the actual moving circular indicator density. -/
theorem circleDensity_joint (h : ℝ) :
    Measurable (fun z : Centers × Circle => circleDensity h z.1.1 z.1.2 z.2) := by
  have hp : MeasurableSet {z : Centers × Circle | z.2 ∈ closedBall z.1.1 (h / 2)} :=
    measurableSet_le (measurable_snd.dist (measurable_fst.comp measurable_fst)) measurable_const
  have hn : MeasurableSet {z : Centers × Circle | z.2 ∈ closedBall z.1.2 (h / 2)} :=
    measurableSet_le (measurable_snd.dist (measurable_snd.comp measurable_fst)) measurable_const
  have hfirst : Measurable ({z : Centers × Circle | z.2 ∈ closedBall z.1.1 (h / 2)}.indicator
      (fun _ => (1 / 2 : ℝ))) := measurable_const.indicator hp
  have hsecond : Measurable ({z : Centers × Circle | z.2 ∈ closedBall z.1.2 (h / 2)}.indicator
      (fun _ => (1 / 2 : ℝ))) := measurable_const.indicator hn
  convert ((measurable_const (a := (1 : ℝ))).add hfirst).sub hsecond using 1
  funext z
  rfl

theorem rowDensity_joint (h : ℝ) :
    Measurable (fun z : Centers × ℝ => (row h z.1.1 z.1.2).density z.2) := by
  have hbody := (circleDensity_joint h).comp
    (measurable_fst.prodMk (AddCircle.measurable_mk'.comp measurable_snd))
  have hsupport : MeasurableSet {z : Centers × ℝ | z.2 ∈ Icc (0 : ℝ) 1} :=
    measurableSet_Icc.preimage measurable_snd
  convert hbody.indicator hsupport using 1
  funext z
  rfl

/-- Joint cumulative values are obtained by integrating jointly measurable
densities over the two oriented interval indicators. The proof works on
arbitrary measurable parameter spaces after composition. -/
theorem rowCumulative_joint (h : ℝ) :
    Measurable (fun z : Centers × ℝ => (row h z.1.1 z.1.2).cumulative z.2) := by
  let f : (Centers × ℝ) × ℝ → ℝ := fun z => (row h z.1.1.1 z.1.1.2).density z.2
  have hg : Measurable (fun z : (Centers × ℝ) × ℝ => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hf : Measurable f := (rowDensity_joint h).comp hg
  let positive : Set ((Centers × ℝ) × ℝ) := {z | 0 < z.2 ∧ z.2 ≤ z.1.2}
  let negative : Set ((Centers × ℝ) × ℝ) := {z | z.1.2 < z.2 ∧ z.2 ≤ 0}
  have hp : MeasurableSet positive :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hn : MeasurableSet negative :=
    (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hplus := ((hf.indicator hp).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hminus := ((hf.indicator hn).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun z : Centers × ℝ => (row h z.1.1 z.1.2).cumulative z.2) =
      (fun z => (∫ t : ℝ, positive.indicator f (z, t)) - ∫ t : ℝ, negative.indicator f (z, t)) := by
    funext z
    unfold Row.cumulative intervalIntegral
    congr 1
    · exact (integral_indicator (μ := volume) (s := Ioc (0 : ℝ) z.2)
        (f := (row h z.1.1 z.1.2).density) measurableSet_Ioc).symm
    · exact (integral_indicator (μ := volume) (s := Ioc z.2 (0 : ℝ))
        (f := (row h z.1.1 z.1.2).density) measurableSet_Ioc).symm
  rw [heq]
  exact hplus.sub hminus

set_option maxHeartbeats 200000 in
/-- The actual value of a variable-size physical output share is jointly
measurable in both centers and the output code. Consequently all finite EF
comparison events are measurable after composing with a measurable run. -/
theorem shareValue_joint {Agent : Type*} [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] (h : ℝ) (i : Agent) :
    Measurable (β := ℝ) (fun z : Centers × Allocation Agent =>
      (row h z.1.1 z.1.2).signedMeasure (z.2.share i)) := by
  let f : (Centers × Allocation Agent) × ℝ → ℝ :=
    (fun z : Centers × ℝ => (row h z.1.1 z.1.2).density z.2) ∘
      (fun z => (z.1.1, z.2))
  have hg : Measurable (fun z : (Centers × Allocation Agent) × ℝ => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hf : Measurable f := (rowDensity_joint h).comp hg
  let owned : Set ((Centers × Allocation Agent) × ℝ) := {z | z.2 ∈ z.1.2.share i}
  have hallocation : Measurable (fun z : (Centers × Allocation Agent) × ℝ => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have howned : MeasurableSet owned := (measurable_share_membership i).preimage hallocation
  have hv := ((hf.indicator howned).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun z : Centers × Allocation Agent =>
      (row h z.1.1 z.1.2).signedMeasure (z.2.share i)) =
      (fun z => ∫ t : ℝ, owned.indicator f (z, t)) := by
    funext z
    rw [Row.signedMeasure_apply _ _ (z.2.share_measurable i)]
    exact (integral_indicator (μ := volume) (s := z.2.share i)
      (f := (row h z.1.1 z.1.2).density) (z.2.share_measurable i)).symm
  rw [heq]
  exact hv

end EnvyFreeResearch.Full.NonnegativeMeasurablePulse

#print axioms EnvyFreeResearch.Full.NonnegativeMeasurablePulse.rowDensity_joint
#print axioms EnvyFreeResearch.Full.NonnegativeMeasurablePulse.rowCumulative_joint
#print axioms EnvyFreeResearch.Full.NonnegativeMeasurablePulse.shareValue_joint
