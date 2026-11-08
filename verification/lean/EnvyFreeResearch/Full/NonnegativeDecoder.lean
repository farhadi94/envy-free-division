import EnvyFreeResearch.Full.NonnegativeDetection
import EnvyFreeResearch.R3QueryLower

namespace EnvyFreeResearch.Full.NonnegativeDecoder

open MeasureTheory Set
open scoped ENNReal

abbrev Circle := NonnegativeCircle.Circle
open NonnegativeShift (first second shiftLaw)
open NonnegativeDetection (observerLaw perturbLaw)

/-- Sampling an independent uniform observer misses any designated owner
with exactly probability `1 - 1/n`, even when that owner depends measurably on
both pulse centers. -/
theorem observer_exception_factor {n : ℕ} (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (exception : ℝ × Circle → Fin n) (hexception : Measurable exception)
    {event : Set (ℝ × Circle)} (hevent : MeasurableSet event) :
    perturbLaw n w {z | z.2 ∈ event ∧ z.1 ≠ exception z.2} =
      (1 - (n : ℝ≥0∞)⁻¹) * shiftLaw w event := by
  let := NonnegativeDetection.observerLaw_probability n hn
  let := NonnegativeShift.shiftLaw_probability w hw
  have hmeas : MeasurableSet {z : Fin n × (ℝ × Circle) |
      z.2 ∈ event ∧ z.1 ≠ exception z.2} :=
    (hevent.preimage measurable_snd).inter
      (measurableSet_eq_fun measurable_fst (hexception.comp measurable_snd)).compl
  rw [perturbLaw, Measure.prod_apply_symm hmeas]
  have hsection (parameters : ℝ × Circle) :
      observerLaw n ((fun i => (i, parameters)) ⁻¹'
        {z | z.2 ∈ event ∧ z.1 ≠ exception z.2}) =
      event.indicator (fun _ => (1 - (n : ℝ≥0∞)⁻¹)) parameters := by
    by_cases he : parameters ∈ event
    · have heq : (fun i => (i, parameters)) ⁻¹'
          {z | z.2 ∈ event ∧ z.1 ≠ exception z.2} = {exception parameters}ᶜ := by
        ext i
        simp [he]
      rw [heq, measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
        measure_univ, indicator_of_mem he]
      simp [observerLaw]
    · have heq : (fun i => (i, parameters)) ⁻¹'
          {z | z.2 ∈ event ∧ z.1 ≠ exception z.2} = ∅ := by
        ext i
        simp [he]
      simp [heq, he]
  simp_rw [hsection]
  exact lintegral_indicator_const hevent _

/-- The actual geometric decoder event, for any finite-union equal-length
partition encoded by its measurable owner map. `favorable` may be either
center: the first is favorable for cake and the second for chores. -/
theorem decoder_probability_lower {n : ℕ} (hn : 0 < n) (w : ℝ)
    (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    (owner : Circle → Fin n) (howner : Measurable owner)
    (hfibers : ∀ agent, volume (owner ⁻¹' {agent}) = (n : ℝ≥0∞)⁻¹)
    (favorable : ℝ × Circle → Circle) (hfavorable : Measurable favorable) :
    (1 - (n : ℝ≥0∞)⁻¹) *
      (1 - (ENNReal.ofReal (2 * w))⁻¹ * (n : ℝ≥0∞)⁻¹) ≤
    perturbLaw n w {z | owner (first z.2) ≠ owner (second z.2) ∧
      z.1 ≠ owner (favorable z.2)} := by
  let := NonnegativeShift.shiftLaw_probability w hw
  have hsame : MeasurableSet {z | owner (first z) = owner (second z)} :=
    measurableSet_eq_fun (howner.comp NonnegativeShift.measurable_first)
      (howner.comp NonnegativeShift.measurable_second)
  have hdiff : MeasurableSet {z | owner (first z) ≠ owner (second z)} := hsame.compl
  have hfactor := observer_exception_factor hn w hw (owner ∘ favorable) (howner.comp hfavorable) hdiff
  simp only [mem_ofPred_eq, Function.comp_apply] at hfactor
  rw [hfactor]
  gcongr
  have hbound := NonnegativeShift.same_owner_le owner howner _ hfibers w hw hwsmall
  have heq : {z | owner (first z) ≠ owner (second z)} =
      {z | owner (first z) = owner (second z)}ᶜ := rfl
  rw [heq, measure_compl hsame (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hbound 1

end EnvyFreeResearch.Full.NonnegativeDecoder

#print axioms EnvyFreeResearch.Full.NonnegativeDecoder.observer_exception_factor
#print axioms EnvyFreeResearch.Full.NonnegativeDecoder.decoder_probability_lower
