import EnvyFreeResearch.Full.UpperEnvelope

/-! The maximum-cell envelope applied to the concrete correction sampler. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperEnvelopeStage

open UpperCircular UpperCircularStage UpperRecordedDomain UpperUnionMeasurable
  UpperStageMeasurable UpperUnionCircular UpperCorrectionStage UpperEnvelope UpperPayments Chores

variable {n : ℕ} {Cell : Type*} [Fintype Cell]

/-- An estimated failure for any observer is covered by one envelope event.
The bound contains the sampled-cell count, with no extra observer factor. -/
theorem estimated_failure_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (cells : List Component)
    (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
    (hcache : ∀ c ∈ cells, cached c = mass (μ cutter) c)
    (hpositive : 0 < (μ cutter).real (domain cells))
    (a : Fin n → Cell → ℝ) (rho : Cell → Measure ℝ)
    [∀ e, IsZeroOrProbabilityMeasure (rho e)]
    (eps lam : ℝ) (heps : 0 ≤ eps) (hfit : eps ≤ (μ cutter).real (domain cells))
    (hsupply : 1 / 2 ≤ (μ cutter).real (domain cells)) (hlam : 0 < lam) :
    (volume : Measure UpperCircular.Circle) {start | ∃ i,
      lam * cellGap a i cutter / 4 < |estimate a rho i cutter
        (piece policy history cutter cached ((μ cutter).real (domain cells)) cells
          (fraction eps _ heps hfit hpositive) start)|} ≤
      ENNReal.ofReal (8 * eps * Fintype.card Cell / lam) := by
  calc
    _ ≤ (volume : Measure UpperCircular.Circle) {start | lam / 4 <
        (envelope a rho cutter).real
          (piece policy history cutter cached ((μ cutter).real (domain cells)) cells
            (fraction eps _ heps hfit hpositive) start)} := by
      apply measure_mono
      intro start hbad
      exact estimated_exceed_implies_envelope a rho cutter _ lam hbad
    _ ≤ _ := foreign_exceed_probability μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive hmeas eps (Fintype.card Cell) lam heps hfit hsupply hlam
      (envelope a rho cutter) (envelope_mass_le a rho cutter (domain cells))

end EnvyFreeResearch.Full.UpperEnvelopeStage
