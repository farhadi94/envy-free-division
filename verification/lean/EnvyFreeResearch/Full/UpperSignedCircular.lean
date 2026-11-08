import EnvyFreeResearch.Full.UpperPhysical

/-!
# Signed foreign-mass identities for actual circular Cut pieces

Finite foreign measures give integrable real mass random variables. Applying
the physical inclusion identity to the two Jordan parts proves the signed
expectation identity; applying it to total variation proves the absolute-value
bound. Thus neither identity is an assumed oracle primitive.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperSignedCircular

open UpperCircular UpperPhysical
abbrev Circle := UpperCircular.Circle

variable (domain : Set ℝ) (hdomain : MeasurableSet domain) (amount : I)
  (first last : Circle → ℝ) (hfirstMeas : Measurable first) (hlastMeas : Measurable last)

include hdomain hfirstMeas hlastMeas

theorem physical_piece_measurable (start : Circle) :
    MeasurableSet (physicalPiece domain amount start (first start) (last start)) := by
  exact (measurable_physical_membership domain hdomain amount first last
    hfirstMeas hlastMeas).preimage (measurable_const.prodMk measurable_id)

theorem foreign_mass_measurable (foreign : Measure ℝ) [SFinite foreign] :
    Measurable (fun start => foreign
      (physicalPiece domain amount start (first start) (last start))) := by
  exact measurable_measure_prodMk_left
    (measurable_physical_membership domain hdomain amount first last hfirstMeas hlastMeas)

theorem foreign_real_mass_integrable (foreign : Measure ℝ) [IsFiniteMeasure foreign] :
    Integrable (fun start => foreign.real
      (physicalPiece domain amount start (first start) (last start)))
      (volume : Measure Circle) := by
  apply (integrable_const (foreign.real domain)).mono'
    (foreign_mass_measurable domain hdomain amount first last hfirstMeas hlastMeas
      foreign).ennreal_toReal.aestronglyMeasurable
  exact ae_of_all _ (fun start => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_mono (physicalPiece_subset domain amount start _ _))

variable {F : ℝ → ℝ} (hF : Monotone F)
  (hrange : ∀ x ∈ domain, 0 ≤ F x ∧ F x ≤ 1)
  (hfirst : ∀ᵐ start ∂(volume : Measure Circle), F (first start) = (value start : ℝ))
  (hlast : ∀ᵐ start ∂(volume : Measure Circle),
    F (last start) = (value (start + project amount) : ℝ))

include hF hrange hfirst hlast in
theorem foreign_real_mass_expectation (foreign : Measure ℝ) [IsFiniteMeasure foreign] :
    (∫ start, foreign.real (physicalPiece domain amount start (first start) (last start))
      ∂(volume : Measure Circle)) = (amount : ℝ) * foreign.real domain := by
  change (∫ start, (foreign (physicalPiece domain amount start
    (first start) (last start))).toReal ∂(volume : Measure Circle)) = _
  rw [integral_toReal
    (foreign_mass_measurable domain hdomain amount first last hfirstMeas hlastMeas
      foreign).aemeasurable
    (ae_of_all _ (fun _ => measure_lt_top foreign _))]
  rw [physical_foreign_mass_expectation domain hdomain foreign amount first last
    hfirstMeas hlastMeas hF hrange hfirst hlast,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal amount.property.1]
  rfl

theorem signed_mass_integrable (signed : SignedMeasure ℝ) :
    Integrable (fun start => signed
      (physicalPiece domain amount start (first start) (last start)))
      (volume : Measure Circle) := by
  have hpos := foreign_real_mass_integrable domain hdomain amount first last
    hfirstMeas hlastMeas signed.toJordanDecomposition.posPart
  have hneg := foreign_real_mass_integrable domain hdomain amount first last
    hfirstMeas hlastMeas signed.toJordanDecomposition.negPart
  apply (hpos.sub hneg).congr
  exact ae_of_all _ (fun start =>
    (signed.apply_eq_posPart_real_sub_negPart_real
      (physical_piece_measurable domain hdomain amount first last hfirstMeas hlastMeas start)).symm)

include hF hrange hfirst hlast in
/-- Exact expectation for an arbitrary finite signed foreign measure, evaluated
on the actual interval/complement pieces determined by the Cut responses. -/
theorem signed_mass_expectation (signed : SignedMeasure ℝ) :
    (∫ start, signed (physicalPiece domain amount start (first start) (last start))
      ∂(volume : Measure Circle)) = (amount : ℝ) * signed domain := by
  have hpos := foreign_real_mass_integrable domain hdomain amount first last
    hfirstMeas hlastMeas signed.toJordanDecomposition.posPart
  have hneg := foreign_real_mass_integrable domain hdomain amount first last
    hfirstMeas hlastMeas signed.toJordanDecomposition.negPart
  have heq : (fun start => signed (physicalPiece domain amount start (first start) (last start))) =
      fun start => signed.toJordanDecomposition.posPart.real
        (physicalPiece domain amount start (first start) (last start)) -
      signed.toJordanDecomposition.negPart.real
        (physicalPiece domain amount start (first start) (last start)) := by
    funext start
    exact signed.apply_eq_posPart_real_sub_negPart_real
      (physical_piece_measurable domain hdomain amount first last hfirstMeas hlastMeas start)
  rw [heq, integral_sub hpos hneg,
    foreign_real_mass_expectation domain hdomain amount first last hfirstMeas hlastMeas
      hF hrange hfirst hlast,
    foreign_real_mass_expectation domain hdomain amount first last hfirstMeas hlastMeas
      hF hrange hfirst hlast,
    signed.apply_eq_posPart_real_sub_negPart_real hdomain]
  ring

include hF hrange hfirst hlast in
/-- The absolute correction error has the total-variation expectation bound
used by the randomized construction. Integrability is proved above. -/
theorem signed_absolute_mass_expectation_le (signed : SignedMeasure ℝ) :
    (∫ start, |signed (physicalPiece domain amount start (first start) (last start))|
      ∂(volume : Measure Circle)) ≤ (amount : ℝ) * signed.totalVariation.real domain := by
  calc
    _ ≤ ∫ start, signed.totalVariation.real
        (physicalPiece domain amount start (first start) (last start))
        ∂(volume : Measure Circle) := by
      apply integral_mono
        (signed_mass_integrable domain hdomain amount first last hfirstMeas hlastMeas signed).abs
        (foreign_real_mass_integrable domain hdomain amount first last hfirstMeas hlastMeas
          signed.totalVariation)
      intro start
      simpa only [Real.norm_eq_abs] using signed.norm_le_totalVariation
        (physicalPiece domain amount start (first start) (last start))
    _ = _ := foreign_real_mass_expectation domain hdomain amount first last hfirstMeas hlastMeas
      hF hrange hfirst hlast signed.totalVariation

end EnvyFreeResearch.Full.UpperSignedCircular
