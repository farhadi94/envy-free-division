import Mathlib

/-!
# The actual continuous law of nearby circular pulse centers

The law is normalized Haar product measure restricted to pairs at circular
distance at most `w`. For `0 < w ≤ 1/2`, this is the same joint law as choosing
`X` uniformly on the unit circle and `Y` uniformly in its length-`2w`
neighborhood. No finite support discretization is used.
-/

namespace EnvyFreeResearch.Full.NonnegativeCircle

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Circle := UnitAddCircle

instance circleProbability : IsProbabilityMeasure (volume : Measure Circle) :=
  ⟨UnitAddCircle.measure_univ⟩

def band (w : ℝ) : Set (Circle × Circle) := {z | dist z.1 z.2 ≤ w}

theorem measurable_band (w : ℝ) : MeasurableSet (band w) :=
  measurableSet_le (measurable_fst.dist measurable_snd) measurable_const

noncomputable def centerLaw (w : ℝ) : Measure (Circle × Circle) :=
  (ENNReal.ofReal (2 * w))⁻¹ •
    ((volume : Measure Circle).prod volume).restrict (band w)

theorem circle_ball_mass (x : Circle) (w : ℝ) (hw : w ≤ 1 / 2) :
    volume (closedBall x w) = ENNReal.ofReal (2 * w) := by
  rw [AddCircle.volume_closedBall]
  congr 1
  exact min_eq_right (by linarith)

theorem first_marginal (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    {A : Set Circle} (hA : MeasurableSet A) :
    centerLaw w (Prod.fst ⁻¹' A) = volume A := by
  have htwo : ENNReal.ofReal (2 * w) ≠ 0 := by positivity
  have hmass : ((volume : Measure Circle).prod volume)
      ((Prod.fst ⁻¹' A) ∩ band w) = ENNReal.ofReal (2 * w) * volume A := by
    rw [Measure.prod_apply ((hA.preimage measurable_fst).inter (measurable_band w))]
    have hsection (x : Circle) :
        volume (Prod.mk x ⁻¹' ((Prod.fst ⁻¹' A) ∩ band w)) =
          A.indicator (fun _ => ENNReal.ofReal (2 * w)) x := by
      by_cases hx : x ∈ A
      · have heq : Prod.mk x ⁻¹' ((Prod.fst ⁻¹' A) ∩ band w) = closedBall x w := by
          ext y
          simp [band, hx, mem_closedBall, dist_comm]
        rw [heq, indicator_of_mem hx]
        exact circle_ball_mass x w hwsmall
      · have heq : Prod.mk x ⁻¹' ((Prod.fst ⁻¹' A) ∩ band w) = ∅ := by
          ext y
          simp [hx]
        simp [heq, hx]
    simp_rw [hsection]
    exact lintegral_indicator_const hA _
  rw [centerLaw, Measure.smul_apply, Measure.restrict_apply (hA.preimage measurable_fst), hmass]
  simp only [smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel htwo ENNReal.ofReal_ne_top, one_mul]

theorem second_marginal (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    {A : Set Circle} (hA : MeasurableSet A) :
    centerLaw w (Prod.snd ⁻¹' A) = volume A := by
  have htwo : ENNReal.ofReal (2 * w) ≠ 0 := by positivity
  have hmass : ((volume : Measure Circle).prod volume)
      ((Prod.snd ⁻¹' A) ∩ band w) = ENNReal.ofReal (2 * w) * volume A := by
    rw [Measure.prod_apply_symm ((hA.preimage measurable_snd).inter (measurable_band w))]
    have hsection (y : Circle) :
        volume ((fun x => (x, y)) ⁻¹' ((Prod.snd ⁻¹' A) ∩ band w)) =
          A.indicator (fun _ => ENNReal.ofReal (2 * w)) y := by
      by_cases hy : y ∈ A
      · have heq : (fun x => (x, y)) ⁻¹' ((Prod.snd ⁻¹' A) ∩ band w) = closedBall y w := by
          ext x
          simp [band, hy, mem_closedBall]
        rw [heq, indicator_of_mem hy]
        exact circle_ball_mass y w hwsmall
      · have heq : (fun x => (x, y)) ⁻¹' ((Prod.snd ⁻¹' A) ∩ band w) = ∅ := by
          ext x
          simp [hy]
        simp [heq, hy]
    simp_rw [hsection]
    exact lintegral_indicator_const hA _
  rw [centerLaw, Measure.smul_apply, Measure.restrict_apply (hA.preimage measurable_snd), hmass]
  simp only [smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel htwo ENNReal.ofReal_ne_top, one_mul]

theorem centerLaw_probability (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    IsProbabilityMeasure (centerLaw w) := by
  constructor
  simpa only [preimage_univ, measure_univ] using
    first_marginal w hw hwsmall MeasurableSet.univ

/-- Any ownership map whose fibers all have mass `b` has probability of equal
owners at most `b/(2w)`. Component counts and geometry of the bundles do not
enter this bound. -/
theorem same_owner_le {Agent : Type*} [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [Countable Agent]
    (owner : Circle → Agent) (howner : Measurable owner) (b : ℝ≥0∞)
    (hfibers : ∀ agent, volume (owner ⁻¹' {agent}) = b) (w : ℝ) :
    centerLaw w {z | owner z.1 = owner z.2} ≤
      (ENNReal.ofReal (2 * w))⁻¹ * b := by
  have hmeas : MeasurableSet {z : Circle × Circle | owner z.1 = owner z.2} :=
    measurableSet_eq_fun (howner.comp measurable_fst) (howner.comp measurable_snd)
  have hmass : ((volume : Measure Circle).prod volume)
      {z : Circle × Circle | owner z.1 = owner z.2} = b := by
    rw [Measure.prod_apply hmeas]
    have hsection (x : Circle) : volume
        (Prod.mk x ⁻¹' {z : Circle × Circle | owner z.1 = owner z.2}) = b := by
      have heq : Prod.mk x ⁻¹' {z : Circle × Circle | owner z.1 = owner z.2} =
          owner ⁻¹' {owner x} := by
        ext y
        simp [eq_comm]
      rw [heq]
      exact hfibers (owner x)
    simp_rw [hsection]
    simp
  rw [centerLaw, Measure.smul_apply, Measure.restrict_apply hmeas]
  change (ENNReal.ofReal (2 * w))⁻¹ * _ ≤ _
  exact mul_le_mul_right ((measure_mono inter_subset_left).trans_eq hmass) _

end EnvyFreeResearch.Full.NonnegativeCircle

#print axioms EnvyFreeResearch.Full.NonnegativeCircle.first_marginal
#print axioms EnvyFreeResearch.Full.NonnegativeCircle.second_marginal
#print axioms EnvyFreeResearch.Full.NonnegativeCircle.centerLaw_probability
#print axioms EnvyFreeResearch.Full.NonnegativeCircle.same_owner_le
