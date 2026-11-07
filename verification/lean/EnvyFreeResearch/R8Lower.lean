import EnvyFreeResearch.R7Lower

/-!
# Exact finite transcript refinement

The parent map and fine masses are actual finite objects. Interval geometry,
strictly positive density realization, and an all-real-query game are external.
-/

namespace EnvyFreeResearch.R8Lower

open scoped BigOperators

section Refinement

variable {Coarse Fine Agent : Type*} [Fintype Coarse] [Fintype Fine]
  [DecidableEq Coarse]

def aggregate (parent : Fine → Coarse) (mass : Fine → ℝ) (c : Coarse) : ℝ :=
  ∑ t, if parent t = c then mass t else 0

theorem weighted_aggregate (parent : Fine → Coarse) (mass : Fine → ℝ)
    (coefficient : Coarse → ℝ) :
    (∑ c, coefficient c * aggregate parent mass c) =
      ∑ t, coefficient (parent t) * mass t := by
  simp only [aggregate, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [mul_ite]

theorem aggregate_total (parent : Fine → Coarse) (mass : Fine → ℝ) :
    (∑ c, aggregate parent mass c) = ∑ t, mass t := by
  simpa using weighted_aggregate parent mass (fun _ => 1)

omit [Fintype Coarse] in
theorem aggregate_nonnegative (parent : Fine → Coarse) (mass : Fine → ℝ)
    (hmass : ∀ t, 0 ≤ mass t) (c : Coarse) : 0 ≤ aggregate parent mass c := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact hmass t
  · exact le_rfl

omit [Fintype Coarse] in
theorem aggregate_positive (parent : Fine → Coarse) (mass : Fine → ℝ)
    (hparent : Function.Surjective parent) (hmass : ∀ t, 0 < mass t)
    (c : Coarse) : 0 < aggregate parent mass c := by
  obtain ⟨t, ht⟩ := hparent c
  have hterm : (if parent t = c then mass t else 0) ≤ aggregate parent mass c := by
    unfold aggregate
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun u => if parent u = c then mass u else 0) (a := t)
    · intro u _
      split_ifs
      · exact (hmass u).le
      · exact le_rfl
    · exact Finset.mem_univ t
  exact lt_of_lt_of_le (hmass t) (by simpa [ht] using hterm)

omit [Fintype Coarse] in
theorem parent_fiber_positive (parent : Fine → Coarse)
    (hparent : Function.Surjective parent) (c : Coarse) :
    0 < (Finset.univ.filter (fun t => parent t = c)).card := by
  obtain ⟨t, ht⟩ := hparent c
  apply Finset.card_pos.mpr
  exact ⟨t, by simp [ht]⟩

noncomputable def equalRefinement (parent : Fine → Coarse) (mass : Coarse → ℝ)
    (t : Fine) : ℝ :=
  mass (parent t) / ((Finset.univ.filter (fun u => parent u = parent t)).card : ℝ)

omit [Fintype Coarse] in
theorem equal_refinement_positive (parent : Fine → Coarse) (mass : Coarse → ℝ)
    (hparent : Function.Surjective parent) (hmass : ∀ c, 0 < mass c) (t : Fine) :
    0 < equalRefinement parent mass t := by
  apply div_pos (hmass _)
  exact_mod_cast parent_fiber_positive parent hparent (parent t)

omit [Fintype Coarse] in
theorem equal_refinement_aggregate (parent : Fine → Coarse) (mass : Coarse → ℝ)
    (hparent : Function.Surjective parent) (c : Coarse) :
    aggregate parent (equalRefinement parent mass) c = mass c := by
  have hcard : ((Finset.univ.filter (fun t => parent t = c)).card : ℝ) ≠ 0 := by
    exact_mod_cast (parent_fiber_positive parent hparent c).ne'
  unfold aggregate equalRefinement
  have hid (t : Fine) :
      (if parent t = c then
        mass (parent t) / ((Finset.univ.filter (fun u => parent u = parent t)).card : ℝ)
        else 0) =
      if parent t = c then mass c / ((Finset.univ.filter (fun u => parent u = c)).card : ℝ)
        else 0 := by
    split_ifs with ht
    · rw [ht]
    · rfl
  simp_rw [hid]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  field_simp

omit [Fintype Coarse] in
theorem exists_positive_refinement (parent : Fine → Coarse) (mass : Coarse → ℝ)
    (hparent : Function.Surjective parent) (hmass : ∀ c, 0 < mass c) :
    ∃ fineMass : Fine → ℝ, (∀ t, 0 < fineMass t) ∧ aggregate parent fineMass = mass := by
  refine ⟨equalRefinement parent mass, equal_refinement_positive parent mass hparent hmass, ?_⟩
  funext c
  exact equal_refinement_aggregate parent mass hparent c

theorem measurement_equal_iff (parent : Fine → Coarse) (mass : Fine → ℝ)
    (coefficient : Coarse → ℝ) (reply : ℝ) :
    (∑ c, coefficient c * aggregate parent mass c) = reply ↔
      (∑ t, coefficient (parent t) * mass t) = reply := by
  rw [weighted_aggregate]

/-- A strict failure inequality is preserved without revealing its unknown
bracket total as an additional equality record. -/
theorem measurement_strict_iff (parent : Fine → Coarse) (mass : Fine → ℝ)
    (coefficient : Coarse → ℝ) (target : ℝ) :
    (∑ c, coefficient c * aggregate parent mass c) < target ↔
      (∑ t, coefficient (parent t) * mass t) < target := by
  rw [weighted_aggregate]

theorem owner_value_refinement [DecidableEq Agent] (parent : Fine → Coarse)
    (mass : Fine → ℝ) (owner : Coarse → Agent) (recipient : Agent) :
    R7Lower.allocatedValue (aggregate parent mass) owner recipient =
      R7Lower.allocatedValue mass (owner ∘ parent) recipient := by
  have h := weighted_aggregate parent mass
    (fun c => if owner c = recipient then (1 : ℝ) else 0)
  simpa [R7Lower.allocatedValue, ite_mul] using h

theorem owner_comparison_refinement [DecidableEq Agent] (parent : Fine → Coarse)
    (mass : Fine → ℝ) (owner : Coarse → Agent) (own other : Agent) :
    (∑ c, R7Lower.ownershipComparison owner own other c * aggregate parent mass c) =
      ∑ t, R7Lower.ownershipComparison (owner ∘ parent) own other t * mass t := by
  exact weighted_aggregate parent mass (R7Lower.ownershipComparison owner own other)

/-- A coarse word and its literal pullback have the same entire utility
table, hence the same exact EF comparisons, in either orientation. -/
theorem all_owner_comparisons_preserved [DecidableEq Agent]
    (parent : Fine → Coarse) (mass : Agent → Fine → ℝ) (owner : Coarse → Agent) :
    (∀ i j, R7Lower.allocatedValue (aggregate parent (mass i)) owner j ≤
      R7Lower.allocatedValue (aggregate parent (mass i)) owner i) ↔
    (∀ i j, R7Lower.allocatedValue (mass i) (owner ∘ parent) j ≤
      R7Lower.allocatedValue (mass i) (owner ∘ parent) i) := by
  simp_rw [owner_value_refinement]

end Refinement

section UnqueriedRows

variable {Agent : Type*} [DecidableEq Agent]

omit [DecidableEq Agent] in
/-- Each nonsimple unqueried row consumes at least two full-own atoms.
The simple-row count is the actual filter of the supplied finite counts. -/
theorem simple_unqueried_row_count (unqueried : Finset Agent)
    (ownAtoms : Agent → ℕ) (n : ℕ)
    (hpositive : ∀ i ∈ unqueried, 1 ≤ ownAtoms i)
    (hbudget : (∑ i ∈ unqueried, ownAtoms i) ≤ n) :
    2 * unqueried.card ≤ n + (unqueried.filter (fun i => ownAtoms i = 1)).card := by
  have hpoint : ∀ i ∈ unqueried,
      2 ≤ ownAtoms i + (if ownAtoms i = 1 then 1 else 0) := by
    intro i hi
    have h := hpositive i hi
    split_ifs <;> omega
  have h : 2 * unqueried.card ≤ (∑ i ∈ unqueried, ownAtoms i) +
      (unqueried.filter (fun i => ownAtoms i = 1)).card := by
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using Finset.sum_le_sum hpoint
  omega

omit [DecidableEq Agent] in
theorem two_simple_rows_charge (unqueried : Finset Agent)
    (ownAtoms : Agent → ℕ) (n : ℕ)
    (hpositive : ∀ i ∈ unqueried, 1 ≤ ownAtoms i)
    (hbudget : (∑ i ∈ unqueried, ownAtoms i) ≤ n)
    (hsimple : (unqueried.filter (fun i => ownAtoms i = 1)).card ≤ 2) :
    2 * unqueried.card ≤ n + 2 := by
  have h := simple_unqueried_row_count unqueried ownAtoms n hpositive hbudget
  omega

theorem queried_rows_from_two_unqueried (allRows queried : Finset Agent)
    (hsubset : queried ⊆ allRows) (hunqueried : (allRows \ queried).card ≤ 2) :
    allRows.card - 2 ≤ queried.card := by
  rw [Finset.card_sdiff_of_subset hsubset] at hunqueried
  omega

theorem queried_rows_from_unqueried_cap (allRows queried : Finset Agent) (cap : ℕ)
    (hsubset : queried ⊆ allRows) (hunqueried : (allRows \ queried).card ≤ cap) :
    allRows.card - cap ≤ queried.card := by
  rw [Finset.card_sdiff_of_subset hsubset] at hunqueried
  omega

omit [DecidableEq Agent] in
/-- The endpoint and interior-owner length premises come from the geometric
argument. This theorem sums actual finite owner lengths to contradict coverage. -/
theorem two_untouched_length_obstruction (remaining : Finset Agent)
    (length : Agent → ℝ) (endpointLength n Δ : ℝ)
    (hn : 4 ≤ n) (hΔ : 0 < Δ) (hcount : (remaining.card : ℝ) + 2 = n)
    (hendpoints : 2 / n - Δ ≤ endpointLength)
    (hremaining : ∀ i ∈ remaining, 1 / n + Δ ≤ length i)
    (hcomplete : endpointLength + (∑ i ∈ remaining, length i) ≤ 1) : False := by
  have hn0 : n ≠ 0 := by linarith
  have hc : (remaining.card : ℝ) = n - 2 := by linarith
  have hsum : (remaining.card : ℝ) * (1 / n + Δ) ≤ ∑ i ∈ remaining, length i := by
    simpa [mul_add] using Finset.sum_le_sum hremaining
  have hid : 2 / n - Δ + (remaining.card : ℝ) * (1 / n + Δ) =
      1 + (n - 3) * Δ := by
    rw [hc]
    field_simp
    ring
  have hstrict : 0 < (n - 3) * Δ := mul_pos (by linarith) hΔ
  linarith

end UnqueriedRows

section FailureRetention

open SubmissionMonteCarlo

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- Baseline failures and newly decoded successes are disjoint actual sets.
Both persist except on the supplied loss set. -/
theorem retained_failure_mass (weight : Outcome → ℝ)
    (success decoded loss failure : Finset Outcome)
    (hweight : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    (hdecoded : decoded ⊆ success)
    (hpersist : ∀ ω, (ω ∉ success ∨ ω ∈ decoded) → ω ∉ loss → ω ∈ failure) :
    1 - eventMass weight success + eventMass weight decoded - eventMass weight loss ≤
      eventMass weight failure := by
  have hpoint (ω : Outcome) :
      weight ω - (if ω ∈ success then weight ω else 0) +
        (if ω ∈ decoded then weight ω else 0) -
        (if ω ∈ loss then weight ω else 0) ≤
        (if ω ∈ failure then weight ω else 0) := by
    have hsub : ω ∈ decoded → ω ∈ success := fun h => hdecoded h
    have hkeep := hpersist ω
    by_cases hs : ω ∈ success <;> by_cases hd : ω ∈ decoded <;>
      by_cases hl : ω ∈ loss <;> by_cases hf : ω ∈ failure <;>
      simp_all only [not_true_eq_false, not_false_eq_true,
        true_implies, false_implies, or_true, or_false, ite_true, ite_false] <;>
      linarith [hweight ω]
  simpa only [eventMass, Finset.sum_sub_distrib, Finset.sum_add_distrib, htotal] using
    Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)

theorem retained_decoder_ledger (weight : Outcome → ℝ)
    (success decoded loss failure : Finset Outcome) (A : ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    (hdecoded : decoded ⊆ success)
    (hpersist : ∀ ω, (ω ∉ success ∨ ω ∈ decoded) → ω ∉ loss → ω ∈ failure)
    (hgood : eventMass weight success * A ≤ eventMass weight decoded) :
    1 - eventMass weight success + eventMass weight success * A - eventMass weight loss ≤
      eventMass weight failure := by
  have h := retained_failure_mass weight success decoded loss failure
    hweight htotal hdecoded hpersist
  linarith

end FailureRetention

/-- The terminal uncounted illegal call occurs only on baseline failure
tapes. Retaining their weight absorbs its detection contribution. -/
theorem terminal_illegal_absorption (s A p q j c : ℝ)
    (hs : s ≤ 1) (hj : j ≤ 1 - s) (hc : 0 ≤ c) (hslack : c ≤ 1 - A)
    (hledger : 1 - s + s * A - c * (q + j) ≤ 1 - p) :
    p - (1 - A) ≤ c * q := by
  have hjmul := mul_le_mul_of_nonneg_left hj hc
  have hslackmul := mul_le_mul_of_nonneg_right hslack (sub_nonneg.mpr hs)
  nlinarith

noncomputable def decoderFactor (n w : ℝ) : ℝ :=
  (1 - 1 / n) * (1 - 1 / (2 * n * w))

noncomputable def retainedQueryLower (n p w : ℝ) : ℝ :=
  (n / w) * (p - (1 - decoderFactor n w))

noncomputable def retainedWindow (n p : ℝ) : ℝ :=
  (n - 1) / (n * (n * p - 1))

noncomputable def retainedConstant (n p : ℝ) : ℝ :=
  n * (n * p - 1) ^ 2 / (2 * (n - 1))

theorem decoder_slack_ge_window (n w : ℝ) (hn : 2 ≤ n)
    (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    w / n ≤ 1 - decoderFactor n w := by
  have hn0 : 0 < n := by linarith
  have hinv : 1 / n ≤ 1 := (div_le_one hn0).mpr (by linarith)
  have hnonneg : 0 ≤ (1 - 1 / n) / (2 * n * w) := by positivity
  have hbase : w / n ≤ 1 / n :=
    div_le_div_of_nonneg_right (by linarith) hn0.le
  have hid : 1 - decoderFactor n w = 1 / n + (1 - 1 / n) / (2 * n * w) := by
    unfold decoderFactor
    ring
  rw [hid]
  linarith

theorem query_lower_from_retention (n w s p q j : ℝ) (hn : 2 ≤ n)
    (hw : 0 < w) (hwsmall : w ≤ 1 / 2) (hs : s ≤ 1) (hj : j ≤ 1 - s)
    (hledger : 1 - s + s * decoderFactor n w - (w / n) * (q + j) ≤ 1 - p) :
    retainedQueryLower n p w ≤ q := by
  have hn0 : 0 < n := by linarith
  have h := terminal_illegal_absorption s (decoderFactor n w) p q j (w / n)
    hs hj (by positivity) (decoder_slack_ge_window n w hn hw hwsmall) hledger
  unfold retainedQueryLower
  calc
    (n / w) * (p - (1 - decoderFactor n w)) ≤ (n / w) * ((w / n) * q) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = q := by field_simp

theorem retained_window_legal (n p : ℝ) (hn : 1 < n) (hp : 1 < n * p)
    (hlegal : 2 * (n - 1) ≤ n * (n * p - 1)) :
    0 < retainedWindow n p ∧ retainedWindow n p ≤ 1 / 2 := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n * (n * p - 1) := mul_pos hn0 (by linarith)
  constructor
  · exact div_pos (by linarith) hd
  · exact (div_le_iff₀ hd).mpr (by linarith)

theorem retained_optimized_value (n p : ℝ) (hn : 1 < n) (hp : 1 < n * p) :
    retainedQueryLower n p (retainedWindow n p) = retainedConstant n p := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  have hp1 : n * p - 1 ≠ 0 := by linarith
  unfold retainedQueryLower decoderFactor retainedWindow retainedConstant
  field_simp
  ring

theorem retained_square_identity (n p w : ℝ) (hn : 1 < n) (hw : 0 < w) :
    retainedConstant n p - retainedQueryLower n p w =
      (n * (n * p - 1) * w - (n - 1)) ^ 2 / (2 * n * (n - 1) * w ^ 2) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  unfold retainedConstant retainedQueryLower decoderFactor
  field_simp
  ring

theorem retained_window_optimal (n p w : ℝ) (hn : 1 < n) (hw : 0 < w) :
    retainedQueryLower n p w ≤ retainedConstant n p := by
  apply sub_nonneg.mp
  rw [retained_square_identity n p w hn hw]
  apply div_nonneg (sq_nonneg _)
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  positivity

end EnvyFreeResearch.R8Lower

#print axioms EnvyFreeResearch.R8Lower.weighted_aggregate
#print axioms EnvyFreeResearch.R8Lower.aggregate_total
#print axioms EnvyFreeResearch.R8Lower.aggregate_nonnegative
#print axioms EnvyFreeResearch.R8Lower.aggregate_positive
#print axioms EnvyFreeResearch.R8Lower.parent_fiber_positive
#print axioms EnvyFreeResearch.R8Lower.equal_refinement_positive
#print axioms EnvyFreeResearch.R8Lower.equal_refinement_aggregate
#print axioms EnvyFreeResearch.R8Lower.exists_positive_refinement
#print axioms EnvyFreeResearch.R8Lower.measurement_equal_iff
#print axioms EnvyFreeResearch.R8Lower.measurement_strict_iff
#print axioms EnvyFreeResearch.R8Lower.owner_value_refinement
#print axioms EnvyFreeResearch.R8Lower.owner_comparison_refinement
#print axioms EnvyFreeResearch.R8Lower.all_owner_comparisons_preserved
#print axioms EnvyFreeResearch.R8Lower.simple_unqueried_row_count
#print axioms EnvyFreeResearch.R8Lower.two_simple_rows_charge
#print axioms EnvyFreeResearch.R8Lower.queried_rows_from_two_unqueried
#print axioms EnvyFreeResearch.R8Lower.queried_rows_from_unqueried_cap
#print axioms EnvyFreeResearch.R8Lower.two_untouched_length_obstruction
#print axioms EnvyFreeResearch.R8Lower.retained_failure_mass
#print axioms EnvyFreeResearch.R8Lower.retained_decoder_ledger
#print axioms EnvyFreeResearch.R8Lower.terminal_illegal_absorption
#print axioms EnvyFreeResearch.R8Lower.decoder_slack_ge_window
#print axioms EnvyFreeResearch.R8Lower.query_lower_from_retention
#print axioms EnvyFreeResearch.R8Lower.retained_window_legal
#print axioms EnvyFreeResearch.R8Lower.retained_optimized_value
#print axioms EnvyFreeResearch.R8Lower.retained_square_identity
#print axioms EnvyFreeResearch.R8Lower.retained_window_optimal
