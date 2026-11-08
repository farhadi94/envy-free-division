import Mathlib

/-!
# Query counts: measurable success events and unconditional expectation

These results formalize the probability-to-expectation step, on an arbitrary
measurable sample space. Query counts may be infinite. The input/selector
construction giving a small successful finite-horizon event is a separate
hypothesis, not part of these results.
-/

namespace EnvyFreeResearch.QueryProbability

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A successful outcome outside the low-cost event belongs to the cost tail.
No independence or finite-support assumption is used. -/
theorem success_tail_mass {Q : Ω → ℝ≥0∞} {S : Set Ω} {a p δ : ℝ≥0∞}
    (hsuccess : p ≤ μ S) (hshort : μ (S ∩ {ω | Q ω < a}) ≤ δ) :
    p - δ ≤ μ (S ∩ {ω | a ≤ Q ω}) := by
  apply tsub_le_iff_right.mpr
  calc
    p ≤ μ S := hsuccess
    _ ≤ μ (S ∩ {ω | Q ω < a}) + μ (S ∩ {ω | a ≤ Q ω}) := by
      have hcover : S ⊆ (S ∩ {ω | Q ω < a}) ∪ (S ∩ {ω | a ≤ Q ω}) := by
        intro ω hω
        by_cases h : Q ω < a
        · exact Or.inl ⟨hω, h⟩
        · exact Or.inr ⟨hω, le_of_not_gt h⟩
      exact (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ δ + μ (S ∩ {ω | a ≤ Q ω}) := add_le_add hshort le_rfl
    _ = μ (S ∩ {ω | a ≤ Q ω}) + δ := add_comm _ _

/-- The integral lower bound is derived from an actual measurable indicator,
rather than an assumed numerical expectation inequality. The integral is over
all outcomes, including incorrect returns and nontermination. -/
theorem successful_cost_tail_le_lintegral {Q : Ω → ℝ≥0∞} {S : Set Ω}
    (hQ : Measurable Q) (hS : MeasurableSet S) (a : ℝ≥0∞) :
    a * μ (S ∩ {ω | a ≤ Q ω}) ≤ ∫⁻ ω, Q ω ∂μ := by
  have htail : MeasurableSet (S ∩ {ω | a ≤ Q ω}) :=
    hS.inter (measurableSet_le measurable_const hQ)
  rw [← lintegral_indicator_const htail a]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ S ∩ {ω | a ≤ Q ω}
  · simpa only [indicator_of_mem hω] using (show a ≤ Q ω from hω.2)
  · simp only [indicator_of_notMem hω, zero_le]

/-- A success-probability bound and a small successful low-cost event give an
unconditional extended-expectation lower bound, even if its value is infinity.
`p - δ` is truncated subtraction in the nonnegative extended reals. -/
theorem expectation_lower_from_success {Q : Ω → ℝ≥0∞} {S : Set Ω}
    (hQ : Measurable Q) (hS : MeasurableSet S) {a p δ : ℝ≥0∞}
    (hsuccess : p ≤ μ S) (hshort : μ (S ∩ {ω | Q ω < a}) ≤ δ) :
    a * (p - δ) ≤ ∫⁻ ω, Q ω ∂μ := by
  calc
    a * (p - δ) ≤ a * μ (S ∩ {ω | a ≤ Q ω}) := by
      gcongr
      exact success_tail_mass hsuccess hshort
    _ ≤ ∫⁻ ω, Q ω ∂μ := successful_cost_tail_le_lintegral hQ hS a

/-- Extended natural counts have no values strictly between `q` and `q + 1`.
The infinite-count case is included. -/
theorem enat_lt_successor_iff (N : ℕ∞) (q : ℕ) :
    (N : ℝ≥0∞) < ((q + 1 : ℕ) : ℝ≥0∞) ↔ N ≤ (q : ℕ∞) := by
  refine ENat.recTopCoe ?_ (fun n => ?_) N
  · simp
  · norm_cast
    omega

/-- The manuscript's exact `(q + 1) (p - δ)` bound for a measurable query
count taking values in `ℕ ∪ {∞}`. There is no assumption of termination,
finite expectation, zero error, or independence. `S` denotes legal correct
finite return; its semantic interpretation is supplied by the caller. -/
theorem enat_expectation_lower_from_success {Q : Ω → ℕ∞} {S : Set Ω}
    (hQ : Measurable Q) (hS : MeasurableSet S) (q : ℕ) {p δ : ℝ≥0∞}
    (hsuccess : p ≤ μ S) (hshort : μ (S ∩ {ω | Q ω ≤ (q : ℕ∞)}) ≤ δ) :
    ((q + 1 : ℕ) : ℝ≥0∞) * (p - δ) ≤ ∫⁻ ω, (Q ω : ℝ≥0∞) ∂μ := by
  have hQ' : Measurable (fun ω => (Q ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp hQ
  apply expectation_lower_from_success hQ' hS hsuccess
  simpa only [enat_lt_successor_iff] using hshort

/-- Finite-valued query counts are a specialization of the same integral
argument; the expectation can still be infinite on an infinite sample space. -/
theorem nat_expectation_lower_from_success {Q : Ω → ℕ} {S : Set Ω}
    (hQ : Measurable Q) (hS : MeasurableSet S) (q : ℕ) {p δ : ℝ≥0∞}
    (hsuccess : p ≤ μ S) (hshort : μ (S ∩ {ω | Q ω ≤ q}) ≤ δ) :
    ((q + 1 : ℕ) : ℝ≥0∞) * (p - δ) ≤ ∫⁻ ω, (Q ω : ℝ≥0∞) ∂μ := by
  have hQ' : Measurable (fun ω => (Q ω : ℕ∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℕ∞))).comp hQ
  simpa only [ENat.toENNReal_coe, Nat.cast_le] using
    (enat_expectation_lower_from_success hQ' hS q hsuccess (by simpa using hshort))

/-- If each cutoff has some fixed input with a small successful short-run
event, the supremum of the unconditional expectations is infinite. The input
may depend on the cutoff; no single input of infinite expectation is asserted. -/
theorem supremum_expectations_eq_top {I : Type*} (Q : I → Ω → ℕ∞)
    (S : I → Set Ω) (hQ : ∀ i, Measurable (Q i))
    (hS : ∀ i, MeasurableSet (S i)) {p δ : ℝ≥0∞} (hgap : δ < p)
    (hsuccess : ∀ i, p ≤ μ (S i))
    (hhard : ∀ q : ℕ, ∃ i, μ (S i ∩ {ω | Q i ω ≤ (q : ℕ∞)}) ≤ δ) :
    (⨆ i, ∫⁻ ω, (Q i ω : ℝ≥0∞) ∂μ) = ∞ := by
  have hq (q : ℕ) :
      (q : ℝ≥0∞) * (p - δ) ≤ ⨆ i, ∫⁻ ω, (Q i ω : ℝ≥0∞) ∂μ := by
    obtain ⟨i, hi⟩ := hhard q
    calc
      (q : ℝ≥0∞) * (p - δ) ≤ ((q + 1 : ℕ) : ℝ≥0∞) * (p - δ) := by
        gcongr
        exact Nat.le_add_right q 1
      _ ≤ ∫⁻ ω, (Q i ω : ℝ≥0∞) ∂μ :=
        enat_expectation_lower_from_success (hQ i) (hS i) q (hsuccess i) hi
      _ ≤ ⨆ i, ∫⁻ ω, (Q i ω : ℝ≥0∞) ∂μ :=
        le_iSup (fun j : I => ∫⁻ ω, (Q j ω : ℝ≥0∞) ∂μ) i
  apply top_unique
  calc
    ∞ = (⨆ q : ℕ, (q : ℝ≥0∞)) * (p - δ) := by
      simp [ENNReal.iSup_natCast, ne_of_gt (tsub_pos_iff_lt.mpr hgap)]
    _ = ⨆ q : ℕ, (q : ℝ≥0∞) * (p - δ) := ENNReal.iSup_mul _ _
    _ ≤ ⨆ i, ∫⁻ ω, (Q i ω : ℝ≥0∞) ∂μ := iSup_le hq

/-! ## Survival events and expected waiting time -/

/-- The event that more than `n` attempts are needed. Infinity represents an
execution that never succeeds and continues to make attempts. -/
def survival (T : Ω → ℕ∞) (n : ℕ) : Set Ω := {ω | (n : ℕ∞) < T ω}

theorem measurable_survival {T : Ω → ℕ∞} (hT : Measurable T) (n : ℕ) :
    MeasurableSet (survival T n) :=
  (MeasurableSet.of_discrete : MeasurableSet {N : ℕ∞ | (n : ℕ∞) < N}).preimage hT

/-- Pointwise tail-sum identity for an extended natural count. -/
theorem enat_eq_tsum_tails (N : ℕ∞) :
    (N : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < N then (1 : ℝ≥0∞) else 0 := by
  classical
  refine ENat.recTopCoe ?_ (fun k => ?_) N
  · simp only [ENat.toENNReal_top, ENat.natCast_lt_top, ite_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  · simp only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
    rw [tsum_eq_sum (s := Finset.range k) (by
      intro n hn
      have hn' : ¬ n < k := by simpa only [Finset.mem_range] using hn
      simp only [hn', ite_false])]
    symm
    calc
      (∑ n ∈ Finset.range k, if n < k then (1 : ℝ≥0∞) else 0) =
          ∑ _n ∈ Finset.range k, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range.mp hn, ite_true]
      _ = (k : ℝ≥0∞) := by simp

/-- Tonelli's theorem applied to the actual survival indicators yields the
tail-sum formula, including infinite counts and infinite expectation. -/
theorem lintegral_enat_eq_tsum_survival {T : Ω → ℕ∞} (hT : Measurable T) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) = ∑' n : ℕ, μ (survival T n) := by
  classical
  calc
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) =
        ∫⁻ ω, ∑' n : ℕ, (survival T n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      apply lintegral_congr
      intro ω
      simpa only [survival, indicator_apply, mem_ofPred_eq] using enat_eq_tsum_tails (T ω)
    _ = ∑' n : ℕ, ∫⁻ ω, (survival T n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      apply lintegral_tsum
      intro n
      exact (measurable_const.indicator (measurable_survival hT n)).aemeasurable
    _ = ∑' n : ℕ, μ (survival T n) := by
      apply tsum_congr
      intro n
      simp only [lintegral_indicator_const (measurable_survival hT n), one_mul]

/-- An explicit survival-mass contraction implies a geometric tail. It is the
measure consequence of a uniform conditional chance of progress; independence
between attempts is not assumed. -/
theorem survival_mass_le_geometric {T : Ω → ℕ∞} {r : ℝ≥0∞}
    (hstep : ∀ n : ℕ, μ (survival T (n + 1)) ≤ r * μ (survival T n))
    (n : ℕ) : μ (survival T n) ≤ r ^ n * μ (survival T 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      μ (survival T (n + 1)) ≤ r * μ (survival T n) := hstep n
      _ ≤ r * (r ^ n * μ (survival T 0)) := by gcongr
      _ = r ^ (n + 1) * μ (survival T 0) := by rw [pow_succ']; ac_rfl

/-- Geometric survival bounds control the actual extended waiting-time
integral. No finiteness or summability of the expectation is presupposed. -/
theorem waiting_time_expectation_le {T : Ω → ℕ∞} (hT : Measurable T) {r : ℝ≥0∞}
    (hstep : ∀ n : ℕ, μ (survival T (n + 1)) ≤ r * μ (survival T n)) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ (1 - r)⁻¹ * μ (survival T 0) := by
  rw [lintegral_enat_eq_tsum_survival hT]
  calc
    (∑' n : ℕ, μ (survival T n)) ≤
        ∑' n : ℕ, r ^ n * μ (survival T 0) :=
      ENNReal.tsum_le_tsum (survival_mass_le_geometric hstep)
    _ = (1 - r)⁻¹ * μ (survival T 0) := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- On a probability space the initial survival mass is at most one. -/
theorem probability_waiting_time_expectation_le [IsProbabilityMeasure μ]
    {T : Ω → ℕ∞} (hT : Measurable T) {r : ℝ≥0∞}
    (hstep : ∀ n : ℕ, μ (survival T (n + 1)) ≤ r * μ (survival T n)) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ (1 - r)⁻¹ := by
  calc
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ (1 - r)⁻¹ * μ (survival T 0) :=
      waiting_time_expectation_le hT hstep
    _ ≤ (1 - r)⁻¹ * 1 := by
      gcongr
      exact prob_le_one
    _ = (1 - r)⁻¹ := mul_one _

/-- A deterministic per-attempt budget bounds the unconditional expected
total cost. The pointwise budget is supplied explicitly; the expectation
bound itself is obtained by integration. -/
theorem expected_cost_le_of_attempt_budget [IsProbabilityMeasure μ]
    {T : Ω → ℕ∞} (hT : Measurable T) {r b : ℝ≥0∞}
    (hstep : ∀ n : ℕ, μ (survival T (n + 1)) ≤ r * μ (survival T n))
    {C : Ω → ℝ≥0∞} (hcost : ∀ ω, C ω ≤ b * (T ω : ℝ≥0∞)) :
    (∫⁻ ω, C ω ∂μ) ≤ b * (1 - r)⁻¹ := by
  have hT' : Measurable (fun ω => (T ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp hT
  calc
    (∫⁻ ω, C ω ∂μ) ≤ ∫⁻ ω, b * (T ω : ℝ≥0∞) ∂μ := lintegral_mono hcost
    _ = b * ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := lintegral_const_mul b hT'
    _ ≤ b * (1 - r)⁻¹ := by
      gcongr
      exact probability_waiting_time_expectation_le hT hstep

/-- A strict contraction on a finite measure space makes infinite waiting a
null event. This conclusion is proved from the integral bound, not assumed. -/
theorem waiting_time_finite_ae [IsFiniteMeasure μ]
    {T : Ω → ℕ∞} (hT : Measurable T) {r : ℝ≥0∞} (hr : r < 1)
    (hstep : ∀ n : ℕ, μ (survival T (n + 1)) ≤ r * μ (survival T n)) :
    ∀ᵐ ω ∂μ, T ω ≠ ⊤ := by
  have hQ : Measurable (fun ω => (T ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp hT
  have hfinite : (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≠ ∞ :=
    ne_of_lt ((waiting_time_expectation_le hT hstep).trans_lt
      (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hr))
        (measure_lt_top μ _)))
  have hinfinite := measure_eq_top_of_lintegral_ne_top hQ.aemeasurable hfinite
  simpa only [ae_iff, not_not, ENat.toENNReal_eq_top] using hinfinite

end EnvyFreeResearch.QueryProbability


#print axioms EnvyFreeResearch.QueryProbability.success_tail_mass
#print axioms EnvyFreeResearch.QueryProbability.successful_cost_tail_le_lintegral
#print axioms EnvyFreeResearch.QueryProbability.expectation_lower_from_success
#print axioms EnvyFreeResearch.QueryProbability.enat_lt_successor_iff
#print axioms EnvyFreeResearch.QueryProbability.enat_expectation_lower_from_success
#print axioms EnvyFreeResearch.QueryProbability.nat_expectation_lower_from_success
#print axioms EnvyFreeResearch.QueryProbability.supremum_expectations_eq_top
#print axioms EnvyFreeResearch.QueryProbability.measurable_survival
#print axioms EnvyFreeResearch.QueryProbability.enat_eq_tsum_tails
#print axioms EnvyFreeResearch.QueryProbability.lintegral_enat_eq_tsum_survival
#print axioms EnvyFreeResearch.QueryProbability.survival_mass_le_geometric
#print axioms EnvyFreeResearch.QueryProbability.waiting_time_expectation_le
#print axioms EnvyFreeResearch.QueryProbability.probability_waiting_time_expectation_le
#print axioms EnvyFreeResearch.QueryProbability.expected_cost_le_of_attempt_budget
#print axioms EnvyFreeResearch.QueryProbability.waiting_time_finite_ae
