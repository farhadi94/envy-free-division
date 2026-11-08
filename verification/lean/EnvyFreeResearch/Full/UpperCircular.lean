import EnvyFreeResearch.Full.UpperProbability

/-!
# Circular value-coordinate sampling

The value circle has circumference one. Uniform real draws are mapped to this
circle, and the chosen representative is in `(0, 1]`. Every fixed circular shift
has the uniform value law. These facts are proved from Haar invariance and the
explicit fundamental domain, not assumed as a sampling primitive.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperCircular

abbrev Circle := AddCircle (1 : ℝ)

instance circle_probability : IsProbabilityMeasure (volume : Measure Circle) where
  measure_univ := by simp [AddCircle.measure_univ]

/-- Send an ordinary uniform value draw to the value circle. -/
def project (t : I) : Circle := (t.val : Circle)

/-- The representative used for a circular value target; zero is represented
by one, a convention affecting only a null target. -/
def value (z : Circle) : I :=
  ⟨(AddCircle.equivIoc 1 0 z).val,
    (AddCircle.equivIoc 1 0 z).property.1.le,
    by simpa using (AddCircle.equivIoc 1 0 z).property.2⟩

theorem measurable_project : Measurable project :=
  AddCircle.measurable_mk'.comp measurable_subtype_coe

theorem measurable_value : Measurable value := by
  apply Measurable.subtype_mk
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable

theorem project_preserves_volume :
    MeasurePreserving project (volume : Measure I) (volume : Measure Circle) := by
  have hp : MeasurePreserving ((↑) : ℝ → Circle)
      (volume.restrict (Icc 0 1)) (volume : Measure Circle) := by
    simpa only [zero_add, restrict_Ioc_eq_restrict_Icc] using
      AddCircle.measurePreserving_mk (1 : ℝ) 0
  exact hp.comp unitInterval.measurePreserving_coe

theorem value_project_ae :
    (fun t : I => value (project t)) =ᵐ[(volume : Measure I)] id := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with t ht
  have htpos : 0 < (t : ℝ) := by
    have ht0 : (t : ℝ) ≠ 0 := by
      intro h
      exact ht (Subtype.ext h)
    exact lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  apply Subtype.ext
  change ((AddCircle.equivIoc 1 0) ((t : ℝ) : Circle)).val = t.val
  rw [AddCircle.equivIoc_coe_eq (show (t : ℝ) ∈ Ioc (0 : ℝ) (0 + 1) from
    ⟨htpos, by simpa using t.property.2⟩)]

theorem value_preserves_volume :
    MeasurePreserving value (volume : Measure Circle) (volume : Measure I) := by
  refine ⟨measurable_value, ?_⟩
  rw [← project_preserves_volume.map_eq,
    Measure.map_map measurable_value measurable_project]
  change Measure.map (fun t => value (project t)) volume = volume
  rw [Measure.map_congr value_project_ae, Measure.map_id]

/-- Circular endpoint targets are uniform before their common fresh start;
two different endpoint targets need not be independent. -/
theorem shifted_value_preserves_volume (shift : Circle) :
    MeasurePreserving (fun start : Circle => value (start + shift))
      (volume : Measure Circle) (volume : Measure I) :=
  value_preserves_volume.comp (measurePreserving_add_right volume shift)

/-- Every measurable legal-root response to a circular endpoint target has
exactly the cutter's normalized measure as its marginal distribution. -/
theorem circular_endpoint_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (shift : Circle) (root : Circle → ℝ) (hmeas : Measurable root)
    (hlegal : ∀ᵐ start ∂(volume : Measure Circle),
      cdf μ (root start) = (value (start + shift) : ℝ)) :
    HasLaw root μ (volume : Measure Circle) :=
  UpperProbability.arbitrary_legal_root_hasLaw volume μ
    (fun start => value (start + shift))
    (shifted_value_preserves_volume shift).hasLaw root hmeas hlegal

/-- A circular arc expressed in value coordinates. The coordinate map can be
constant on sets carrying positive foreign mass. -/
def piece {X : Type*} (coordinate : X → Circle) (amount : I) (start : Circle) : Set X :=
  {x | value (coordinate x - start) ≤ amount}

/-- Every fixed point is included with probability equal to the requested arc
length, without a condition on the foreign mass at that point. -/
theorem point_inclusion (c : Circle) (amount : I) :
    (volume : Measure Circle) {start | value (c - start) ≤ amount} =
      ENNReal.ofReal (amount : ℝ) := by
  have hp : MeasurePreserving (fun start : Circle => value (c - start))
      (volume : Measure Circle) (volume : Measure I) :=
    value_preserves_volume.comp (volume.measurePreserving_sub_left c)
  have h := hp.measure_preimage (s := Iic amount) measurableSet_Iic.nullMeasurableSet
  simpa only [preimage, mem_Iic, unitInterval.volume_Iic] using h

/-- Tonelli turns point inclusion into the expected foreign-mass identity.
No relation between `foreign` and the cutter's coordinate measure is required:
in particular, `foreign` may charge cutter-null intervals. -/
theorem foreign_mass_expectation {X : Type*} [MeasurableSpace X]
    (foreign : Measure X) [SFinite foreign]
    (coordinate : X → Circle) (hcoordinate : Measurable coordinate) (amount : I) :
    (∫⁻ start, foreign (piece coordinate amount start) ∂(volume : Measure Circle)) =
      ENNReal.ofReal (amount : ℝ) * foreign univ := by
  let S : Set (Circle × X) :=
    {p | value (coordinate p.2 - p.1) ≤ amount}
  have hS : MeasurableSet S :=
    measurableSet_le
      (measurable_value.comp ((hcoordinate.comp measurable_snd).sub measurable_fst))
      measurable_const
  calc
    _ = ((volume : Measure Circle).prod foreign) S :=
      (Measure.prod_apply hS).symm
    _ = ∫⁻ x, (volume : Measure Circle)
        {start | value (coordinate x - start) ≤ amount} ∂foreign :=
      Measure.prod_apply_symm hS
    _ = ∫⁻ _x, ENNReal.ofReal (amount : ℝ) ∂foreign := by
      apply lintegral_congr
      intro x
      exact point_inclusion (coordinate x) amount
    _ = _ := by simp

end EnvyFreeResearch.Full.UpperCircular
