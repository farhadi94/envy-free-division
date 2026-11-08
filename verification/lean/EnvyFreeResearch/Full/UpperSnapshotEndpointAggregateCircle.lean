import EnvyFreeResearch.Full.UpperSnapshotSmallExecution
import EnvyFreeResearch.Full.UpperAggregateInterpolationNormalization

/-! Actual shared-circle endpoint charges. Every endpoint in a group uses
the same start, and later oracle calls retain all earlier answers. The proof
uses only the separately established marginal laws, never endpoint independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation Chores

variable {n J : ℕ}

/-- A positive fraction of the original cutter mass controls the normalized
law of a possibly history-dependent subdomain, before drawing its fresh start. -/
theorem cond_le_original (μ : Measure ℝ) [IsFiniteMeasure μ] (S B : Set ℝ)
    (hsub : S ⊆ B) (hpositive : 0 < μ.real B)
    (fraction : ℝ) (hfraction : 0 < fraction) (hmass : fraction * μ.real B ≤ μ.real S) :
    cond μ S ≤ ENNReal.ofReal (1 / fraction) • cond μ B := by
  have h := cond_le_restrict μ S B hsub (fraction * μ.real B) (mul_pos hfraction hpositive) hmass
  have hi : (μ B)⁻¹ = ENNReal.ofReal ((μ.real B)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hpositive, ofReal_measureReal (measure_ne_top μ B)]
  have heq : ENNReal.ofReal (1 / (fraction * μ.real B)) • μ.restrict B =
      ENNReal.ofReal (1 / fraction) • cond μ B := by
    rw [ProbabilityTheory.cond, smul_smul, hi,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / fraction)]
    congr 2
    simp only [one_div, mul_inv_rev]
    ring
  exact h.trans_eq heq

/-- One original normalized row is dominated by population-size times the
actual sampling mixture, without assuming that the active-label map is injective. -/
theorem row_le_mixture {Row : Type*} [Fintype Row] [Nonempty Row]
    (μ : Fin n → Measure ℝ) (active : Row → Fin n) (cells : List Component) (cutter : Row) :
    cond (μ (active cutter)) (domain cells) ≤
      (Fintype.card Row : ℝ≥0∞) • UpperMixtureSampling.mixture μ active cells := by
  have h := distinct_recipient_budget (fun r => cond (μ (active r)) (domain cells))
    (fun _ : Unit => cutter) (fun _ _ _ => Subsingleton.elim _ _) 1
  simpa [UpperMixtureSampling.mixture] using h

/-- Summing the true marginal laws counts every boundary, including repeats. -/
theorem circle_charge_integral
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (origin : State n) (hgood : WellFormed μ origin)
    (cutter : Fin n) (hpositive : 0 < (μ cutter).real (domain origin.cells))
    (shifts : Fin J → UpperSnapshotSmall.Circle) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ start : UpperSnapshotSmall.Circle,
      ∑ j, u ((UpperSnapshotSmall.execute policy origin cutter shifts start).1 j) ∂volume) =
      (J : ℝ≥0∞) * ∫⁻ z, u z ∂cond (μ cutter) (domain origin.cells) := by
  rw [lintegral_finset_sum]
  · simp_rw [(UpperSnapshotSmall.endpoint_law μ policy hpolicy origin hgood cutter hpositive hmeas shifts _).lintegral_comp hu.aemeasurable]
    simp
  · intro j _
    exact hu.comp ((measurable_pi_apply j).comp (measurable_fst.comp
      (UpperSnapshotSmall.execute_measurable policy hmeas (fun _ => origin) cutter
        (fun _ => shifts) id measurable_const (fun _ => measurable_const) measurable_id)))

/-- Conditional group estimate against the fixed original sampling mixture.
The source state may contain an arbitrary complete preceding query history. -/
theorem circle_charge_le_mixture {Row : Type*} [Fintype Row] [Nonempty Row]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (buffer : List Component) (cutter : Row)
    (hpositive : 0 < (μ (active cutter)).real (domain buffer))
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (origin : State n) (hgood : WellFormed μ origin)
    (hsub : domain origin.cells ⊆ domain buffer)
    (fraction : ℝ) (hfraction : 0 < fraction)
    (hmass : fraction * (μ (active cutter)).real (domain buffer) ≤
      (μ (active cutter)).real (domain origin.cells))
    (shifts : Fin J → UpperSnapshotSmall.Circle) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ start : UpperSnapshotSmall.Circle,
      ∑ j, u ((UpperSnapshotSmall.execute policy origin (active cutter) shifts start).1 j) ∂volume) ≤
      ((J : ℝ≥0∞) * ENNReal.ofReal (1 / fraction) * Fintype.card Row) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active buffer := by
  have hspos := (mul_pos hfraction hpositive).trans_le hmass
  rw [circle_charge_integral μ policy hpolicy hmeas origin hgood _ hspos shifts u hu]
  have hlaw := (cond_le_original (μ (active cutter)) (domain origin.cells) (domain buffer)
    hsub hpositive fraction hfraction hmass).trans
      (smul_le_smul_left (ENNReal.ofReal (1 / fraction)) (row_le_mixture μ active buffer cutter))
  have h := lintegral_mono' hlaw (f := u) le_rfl
  rw [lintegral_smul_measure, lintegral_smul_measure] at h
  exact (mul_le_mul' le_rfl h).trans_eq (by ring)

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
