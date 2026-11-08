import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateTwoCircle
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateParameters

/-! Population-size bounds for the actual two-circle candidate charges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperDomainDifference Chores
variable {n m J : ℕ} [Nonempty (Fin J)]

theorem two_circle_population_charge
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin J → Fin n) (cutter : Fin J)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hlower : 1 / (2 * (J : ℝ)) ≤ t) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ p : UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle,
      ((∑ j, u ((firstRun policy origin (active cutter) cuts selected t p.1).1 j)) +
        ∑ j, u ((secondRun (J := J) policy origin (active cutter) cuts selected t p.1 p.2).1 j))
      ∂((volume : Measure UpperSnapshotSmall.Circle).prod volume)) ≤
      (((J + 2 : ℕ) : ℝ≥0∞) * (2 * (J : ℝ≥0∞)^2)) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells := by
  have hJpos : (0 : ℝ) < J := by
    have hp : 0 < J := lt_of_le_of_lt (Nat.zero_le cutter.val) cutter.isLt
    exact_mod_cast hp
  have htbound : 1 / t ≤ 2 * (J : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * J)).mp hlower
    linarith
  have hcast : ENNReal.ofReal (1 / t) ≤ 2 * (J : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal htbound
  have h := two_circle_charge (J := J) μ active cutter policy hpolicy hmeas origin hgood hpositive
    cuts hzero hmono hsep selected t ht ht2 u hu
  apply h.trans
  apply mul_le_mul' _ le_rfl
  simp only [Fintype.card_fin]
  calc
    _ ≤ ((J+2 : ℕ) : ℝ≥0∞) * (2 * J) * J := mul_le_mul' (mul_le_mul' le_rfl hcast) le_rfl
    _ = _ := by ring

 theorem repeated_population_budget (J : ℕ) (hJ : 2 ≤ J) :
    (16 * J : ℝ≥0∞) * (((J+2 : ℕ) : ℝ≥0∞) * (2 * (J : ℝ≥0∞)^2)) ≤
      ENNReal.ofReal (64 * (J : ℝ)^4) := by
  have hnat : 16*J*((J+2)*(2*J^2)) ≤ 64*J^4 := by
    have h := Nat.mul_le_mul_right (2*J^2) (candidate_endpoint_count J hJ)
    nlinarith
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow, ENNReal.ofReal_natCast]
  exact_mod_cast hnat

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
