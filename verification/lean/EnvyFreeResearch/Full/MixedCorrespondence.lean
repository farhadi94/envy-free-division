import EnvyFreeResearch.Full.MixedLeftmostMain
import EnvyFreeResearch.MixedApproximation

/-! Physical interval values, complete-allocation totals, and the paper's
signed relative approximation predicate. These connect the concrete
leftmost lower bound to finite atomless signed valuations. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedCorrespondence
open Set MeasureTheory IntervalOracle OracleProtocol MixedFrontier MixedExecution
open MixedDensity MixedObstruction MixedPhysicalFailure IntervalAllocation IntervalValues
open MixedSuccess MixedLeftmostMain
open scoped BigOperators Classical ENNReal

variable {Agent Ω : Type*}

theorem value_Ioc (R : Row) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    value R (Ioc a b) = R.cumulative b - R.cumulative a := by
  have hsub : Ioc a b ⊆ Ioc (0 : ℝ) 1 :=
    fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans hb⟩
  rw [value_signedMeasure R _ measurableSet_Ioc, inter_eq_left.mpr hsub]
  exact (R.interval_value hab).symm

theorem value_Icc (R : Row) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    value R (Icc a b) = R.cumulative b - R.cumulative a := by
  rw [value, integral_Icc_eq_integral_Ioc]
  exact value_Ioc R ha hab hb

theorem sum_value_share [Fintype Agent] (R : Row) (A : Allocation Agent) :
    ∑ i, value R (A.share i) = R.cumulative 1 := by
  have hi : Integrable R.density domainMeasure := R.integrable.restrict
  have h := integral_iUnion_fintype (μ := domainMeasure)
    (fun i => A.share_measurable i) (fun i j hij => A.share_disjoint hij)
    (fun _ => hi.integrableOn)
  change (∑ i, ∫ x in A.share i, R.density x ∂domainMeasure) = _
  rw [← h, A.share_cover]
  simpa only [value, Row.cumulative_zero, sub_zero] using
    value_Icc R (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)

def RelativeEF (rows : Agent → Row) (A : Allocation Agent) (α : ℝ) : Prop :=
  ∀ i j, value (rows i) (A.share j) - value (rows i) (A.share i) ≤
    (1 - α) * max |value (rows i) (A.share i)| |value (rows i) (A.share j)|

/-- The equivalence is derived from the total of the actual physical
allocation, rather than assumed for an abstract utility matrix. -/
theorem relative_iff_approximate [Fintype Agent] {α : ℝ}
    (S : State Agent α) (A : Allocation Agent) (hα : 0 < α) (hα1 : α ≤ 1) :
    RelativeEF S.rows A α ↔ ApproximateEF S A 0 := by
  apply MixedApproximation.relative_iff_cake_comparisons
    (fun i j => value (S.rows i) (A.share j)) α hα hα1
  intro i
  rw [sum_value_share, (S.ceiling i).1]
  norm_num

def relativeSuccess [MeasurableSpace Ω]
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) : Set Ω :=
  {ω | ∃ fuel A, (run next (oracle (profile S)) ω fuel []).stop = .returned A ∧
    RelativeEF S.rows A α}

theorem relativeSuccess_eq [Fintype Agent] [MeasurableSpace Ω]
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    {α : ℝ} (S : State Agent α) (hα : 0 < α) (hα1 : α ≤ 1) :
    relativeSuccess next S = success next S 0 := by
  ext ω
  simp only [relativeSuccess, success, mem_ofPred_eq, mem_iUnion,
    MixedAmplification.capSuccess, relative_iff_approximate S _ hα hα1]

/-- Any fixed positive relative approximation and fixed positive success
probability require an unbounded worst-input expectation under least roots. -/
theorem relative_expected_queries_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ}
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hsuccess : ∀ S : State Agent α, ENNReal.ofReal p ≤ μ (relativeSuccess next S)) :
    (⨆ S : State Agent α,
      ∫⁻ ω, (queryCost next (oracle (profile S)) ω [] : ℝ≥0∞) ∂μ) = ∞ := by
  apply expected_queries_unbounded next base hnext 0 p hn hα hα hp
  intro S
  simpa only [relativeSuccess_eq next S hα hα1] using hsuccess S

end EnvyFreeResearch.Full.MixedCorrespondence
