import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointVector
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateBudget

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable Chores
variable {n m J : ℕ}

theorem actual_small_endpoints_population_bound
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin J → Fin n) (cutter : Fin J)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (U : Set ℝ) (hpositive : 0 < (μ (active cutter)).real U)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (score : Fin (m+1) → ℝ) (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hJ : 2≤J)
    (hlower : 1/(2*(J:ℝ))≤t)
    (origin : State n) (hs : smallValid μ U cuts origin) (u : ℝ → ℝ≥0∞) (hu : Measurable u) (hu0 : u 0=0) :
    (∫⁻ tape, ∑ j, u (smallEndpointVector hJ policy (active cutter) cuts score U t origin tape j)
      ∂law (volume.prod volume : Measure (Circle × Circle)) (16*J)) ≤
      ENNReal.ofReal (64*(J:ℝ)^4)*∫⁻ x,u x ∂UpperMixtureSampling.mixture μ active origin.cells := by
  letI : Nonempty (Fin J) := ⟨cutter⟩
  have hJpos : (0:ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have htbound : 1/t≤2*(J:ℝ) := by
    apply (div_le_iff₀ ht).mpr
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<2*J)).mp hlower
    linarith
  have hcast : ENNReal.ofReal (1/t)≤2*(J:ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal htbound
  have hb : (((J+2:ℕ):ℝ≥0∞)*ENNReal.ofReal (1/t)*J) ≤
      (((J+2:ℕ):ℝ≥0∞)*(2*(J:ℝ≥0∞)^2)) := by
    calc
      _ ≤ ((J+2:ℕ):ℝ≥0∞)*(2*J)*J := mul_le_mul' (mul_le_mul' le_rfl hcast) le_rfl
      _ = _ := by ring
  have hr := actual_small_endpoints_expectation μ active cutter policy hpolicy hmeas U hpositive
    cuts hzero hmono score t ht hhalf hJ origin hs u hu hu0
  simp only [Fintype.card_fin] at hr
  apply hr.trans
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ ((16*J:ℕ):ℝ≥0∞)*(((J+2:ℕ):ℝ≥0∞)*(2*(J:ℝ≥0∞)^2)) := mul_le_mul' le_rfl hb
    _ ≤ _ := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using UpperSnapshotEndpointAggregate.repeated_population_budget J hJ

end EnvyFreeResearch.Full.UpperSnapshotRepetition
