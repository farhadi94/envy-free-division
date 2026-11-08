import EnvyFreeResearch.Full.NonnegativeShift
import EnvyFreeResearch.Full.NonnegativeProbability

namespace EnvyFreeResearch.Full.NonnegativeEndpointLaw

open MeasureTheory Set Filter
open scoped ENNReal Topology

abbrev Circle := NonnegativeCircle.Circle

noncomputable def representative (x : Circle) : ℝ :=
  (AddCircle.measurableEquivIoc (1 : ℝ) 0 x).val

theorem measurable_representative : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

theorem representative_injective : Function.Injective representative := by
  intro x y hxy
  apply (AddCircle.measurableEquivIoc (1 : ℝ) 0).injective
  exact Subtype.ext hxy

theorem representative_range (x : Circle) : 0 < representative x ∧ representative x ≤ 1 := by
  simpa only [representative, Set.mem_Ioc, zero_add] using
    (AddCircle.measurableEquivIoc (1 : ℝ) 0 x).property

theorem representative_coe (x : Circle) : (representative x : Circle) = x :=
  AddCircle.coe_equivIoc

theorem representative_fiber_null (a : ℝ) :
    volume (representative ⁻¹' {a}) = 0 := by
  let : NullSingletonClass (volume : Measure Circle) :=
    ⟨NonnegativeShift.circle_singleton_mass⟩
  exact (Set.subsingleton_singleton.preimage representative_injective).measure_zero volume

noncomputable def realFirst (z : ℝ × Circle) : ℝ :=
  representative (NonnegativeShift.first z)

noncomputable def realSecond (z : ℝ × Circle) : ℝ :=
  representative (NonnegativeShift.second z)

theorem measurable_realFirst : Measurable realFirst :=
  measurable_representative.comp NonnegativeShift.measurable_first

theorem measurable_realSecond : Measurable realSecond :=
  measurable_representative.comp NonnegativeShift.measurable_second

theorem realFirst_atomless (w : ℝ) (hw : 0 < w) (a : ℝ) :
    NonnegativeShift.shiftLaw w {z | realFirst z = a} = 0 := by
  change NonnegativeShift.shiftLaw w
    (NonnegativeShift.first ⁻¹' (representative ⁻¹' {a})) = 0
  rw [NonnegativeShift.first_marginal w hw
    ((measurableSet_singleton a).preimage measurable_representative), representative_fiber_null]

theorem realSecond_atomless (w : ℝ) (hw : 0 < w) (a : ℝ) :
    NonnegativeShift.shiftLaw w {z | realSecond z = a} = 0 := by
  change NonnegativeShift.shiftLaw w
    (NonnegativeShift.second ⁻¹' (representative ⁻¹' {a})) = 0
  rw [NonnegativeShift.second_marginal w hw
    ((measurableSet_singleton a).preimage measurable_representative), representative_fiber_null]

/-- The deterministic-width statement instantiated by the actual continuous
perturbation law. The tape space is arbitrary and the finite endpoint count
may have infinite expectation. The width is selected before tape and input
sampling; it is a single natural index, not a random tape-dependent choice. -/
theorem exists_width_for_actual_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : ℝ) (hw : 0 < w)
    (count : Ω → ℕ) (endpoint : Ω → ℕ → ℝ)
    (hcount : Measurable count) (hendpoint : ∀ k, Measurable (fun tape => endpoint tape k))
    {wrong : Set Ω} (hwrong : MeasurableSet wrong) (gap : Ω → ℝ)
    (hgap : Measurable gap) (hpositive : ∀ tape ∈ wrong, 0 < gap tape)
    (width : ℕ → ℝ) (hwidth : ∀ m, 0 < width m)
    (hmono : Antitone width) (hlim : Tendsto width atTop (𝓝 0))
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ m, 0 < width m ∧ width m < 1 ∧
      (μ.prod (NonnegativeShift.shiftLaw w))
        (NonnegativeProbability.endpointHit count endpoint realFirst (width m)) +
      (μ.prod (NonnegativeShift.shiftLaw w))
        (NonnegativeProbability.endpointHit count endpoint realSecond (width m)) +
      μ (wrong ∩ {tape | gap tape ≤ width m}) < η := by
  let := NonnegativeShift.shiftLaw_probability w hw
  exact NonnegativeProbability.exists_one_width count endpoint realFirst realSecond
    hcount hendpoint measurable_realFirst measurable_realSecond
    (realFirst_atomless w hw) (realSecond_atomless w hw)
    hwrong gap hgap hpositive width hwidth hmono hlim η hη

end EnvyFreeResearch.Full.NonnegativeEndpointLaw

#print axioms EnvyFreeResearch.Full.NonnegativeEndpointLaw.realFirst_atomless
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointLaw.realSecond_atomless
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointLaw.exists_width_for_actual_law
