import EnvyFreeResearch.SubmissionMonteCarlo
import EnvyFreeResearch.R4SignedLinear

/-!
# Round 6 finite lower-bound and query-model certificates

This module proves actual finite prefix-table reconstruction, verifier counts,
weighted event/Markov inequalities, the explicit positive-tolerance frontier
constants, and the extension of public-row guards to an arbitrary fixed virtual
query row. Continuous measure realization, oracle replay, arbitrary probability
spaces, and the full adversary are separate handwritten interfaces.
-/

namespace EnvyFreeResearch.R6Lower

open scoped BigOperators
open SubmissionMonteCarlo

section PrefixVerification

variable {Agent : Type*} [DecidableEq Agent]

/-- There are b genuine internal boundaries and b+1 successive cells. -/
def cellMass {b : ℕ} (cumulative : Fin (b + 2) → ℝ) (j : Fin (b + 1)) : ℝ :=
  cumulative j.succ - cumulative j.castSucc

/-- Every cell is assigned to one recipient; a recipient may own many cells
or none. No connected-bundle hypothesis is imposed. -/
def bundleValue {b : ℕ} (cumulative : Fin (b + 2) → ℝ)
    (owner : Fin (b + 1) → Agent) (recipient : Agent) : ℝ :=
  ∑ j, if owner j = recipient then cellMass cumulative j else 0

theorem all_prefixes_determined {b : ℕ} (before after : Fin (b + 2) → ℝ)
    (hzero : before 0 = after 0)
    (htotal : before (Fin.last (b + 1)) = after (Fin.last (b + 1)))
    (hboundary : ∀ j : Fin (b + 2), 0 < j.val → j.val < b + 1 → before j = after j) :
    before = after := by
  funext j
  by_cases hz : j.val = 0
  · have hj : j = 0 := Fin.ext hz
    simpa [hj] using hzero
  · by_cases hl : j.val = b + 1
    · have hj : j = Fin.last (b + 1) := Fin.ext hl
      simpa [hj] using htotal
    · exact hboundary j (by omega) (by have := j.isLt; omega)

/-- Prefix evaluations at the genuine internal boundaries, together with the
known two endpoint values, recover every allocated bundle exactly. -/
theorem all_bundles_determined {b : ℕ} (before after : Fin (b + 2) → ℝ)
    (owner : Fin (b + 1) → Agent)
    (hzero : before 0 = after 0)
    (htotal : before (Fin.last (b + 1)) = after (Fin.last (b + 1)))
    (hboundary : ∀ j : Fin (b + 2), 0 < j.val → j.val < b + 1 → before j = after j) :
    ∀ recipient, bundleValue before owner recipient = bundleValue after owner recipient := by
  rw [all_prefixes_determined before after hzero htotal hboundary]
  exact fun _ => rfl

/-- The reconstructed table certifies actual finite envy comparisons for
every observer, including observers whose own bundle is empty. -/
theorem verified_comparisons_transfer {b : ℕ}
    (actual recorded : Agent → Fin (b + 2) → ℝ) (owner : Fin (b + 1) → Agent)
    (ε : ℝ)
    (hzero : ∀ i, actual i 0 = recorded i 0)
    (htotal : ∀ i, actual i (Fin.last (b + 1)) = recorded i (Fin.last (b + 1)))
    (hboundary : ∀ i (j : Fin (b + 2)), 0 < j.val → j.val < b + 1 →
      actual i j = recorded i j)
    (hverified : ∀ i j, bundleValue (recorded i) owner j ≤
      bundleValue (recorded i) owner i + ε) :
    ∀ i j, bundleValue (actual i) owner j ≤ bundleValue (actual i) owner i + ε := by
  intro i j
  have h := all_bundles_determined (actual i) (recorded i) owner
    (hzero i) (htotal i) (hboundary i)
  rw [h j, h i]
  exact hverified i j

/-- The verifier uses one prefix evaluation for every agent-boundary pair. -/
theorem prefix_query_count {Agent Boundary : Type*} [Fintype Agent] [Fintype Boundary] :
    Fintype.card (Agent × Boundary) = Fintype.card Agent * Fintype.card Boundary :=
  Fintype.card_prod _ _

/-- Actual original calls, at most one guard per call, and all agent-boundary
prefix checks fit the capped verifier budget. -/
theorem capped_verifier_query_bound {Agent Boundary : Type*}
    [Fintype Agent] [Fintype Boundary]
    (original guards q b : ℕ) (horiginal : original ≤ q) (hguards : guards ≤ original)
    (hboundaries : Fintype.card Boundary ≤ b) :
    original + guards + Fintype.card (Agent × Boundary) ≤
      2 * q + Fintype.card Agent * b := by
  rw [Fintype.card_prod]
  have hproduct := Nat.mul_le_mul_left (Fintype.card Agent) hboundaries
  omega

end PrefixVerification

section WeightedEvents

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

def weightedCount (weight : Outcome → ℝ) (count : Outcome → ℕ) : ℝ :=
  ∑ ω, weight ω * (count ω : ℝ)

omit [DecidableEq Outcome] in
theorem weightedCount_nonnegative (weight : Outcome → ℝ) (count : Outcome → ℕ)
    (hweight : ∀ ω, 0 ≤ weight ω) : 0 ≤ weightedCount weight count := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hweight ω) (Nat.cast_nonneg _)

/-- The strict integer-query tail uses q+1, so the statement also handles q=0. -/
theorem query_tail_markov (weight : Outcome → ℝ) (queries : Outcome → ℕ) (q : ℕ)
    (hweight : ∀ ω, 0 ≤ weight ω) :
    eventMass weight (Finset.univ.filter (fun ω => q < queries ω)) ≤
      weightedCount weight queries / (q + 1 : ℝ) := by
  classical
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < q + 1)).mpr
  rw [eventMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hq : q < queries ω
  · simp only [hq, ite_true]
    have hcount : (q + 1 : ℝ) ≤ queries ω := by exact_mod_cast hq
    exact mul_le_mul_of_nonneg_left hcount (hweight ω)
  · simp only [hq, ite_false, zero_mul]
    exact mul_nonneg (hweight ω) (Nat.cast_nonneg _)

/-- A concrete finite-event decomposition: successful runs not in the query
tail and not in the capped-output event must have more than b boundaries. -/
theorem successful_fragmentation_tail (weight : Outcome → ℝ)
    (queries boundaries : Outcome → ℕ) (success : Finset Outcome)
    (q b : ℕ) (p η : ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hsuccess : p ≤ eventMass weight success)
    (hcap : eventMass weight
      (success.filter (fun ω => queries ω ≤ q ∧ boundaries ω ≤ b)) ≤ η) :
    p - η - weightedCount weight queries / (q + 1 : ℝ) ≤
      eventMass weight (success.filter (fun ω => b < boundaries ω)) := by
  classical
  have hdecode : ∀ ω ∈ success,
      ω ∉ Finset.univ.filter (fun ω => q < queries ω) →
      ω ∉ success.filter (fun ω => queries ω ≤ q ∧ boundaries ω ≤ b) →
      ω ∈ success.filter (fun ω => b < boundaries ω) := by
    intro ω hs hq hcapω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hq
    simp only [Finset.mem_filter, hs, true_and] at hcapω ⊢
    omega
  have hdecomp := failure_mass_after_two_exceptions weight success
    (Finset.univ.filter (fun ω => q < queries ω))
    (success.filter (fun ω => queries ω ≤ q ∧ boundaries ω ≤ b))
    (success.filter (fun ω => b < boundaries ω)) hweight hdecode
  have hmarkov := query_tail_markov weight queries q hweight
  linarith

/-- Combining actual finite Markov accounting and the capped-verifier return
bound gives a positive successful-fragmentation tail. -/
theorem half_success_fragmentation_tail (weight : Outcome → ℝ)
    (queries boundaries : Outcome → ℕ) (success : Finset Outcome)
    (q b : ℕ) (p T : ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hsuccess : p ≤ eventMass weight success)
    (hcap : eventMass weight
      (success.filter (fun ω => queries ω ≤ q ∧ boundaries ω ≤ b)) ≤ p / 4)
    (hexpected : weightedCount weight queries ≤ T)
    (hlarge : 4 * T ≤ p * (q + 1 : ℝ)) :
    p / 2 ≤ eventMass weight (success.filter (fun ω => b < boundaries ω)) := by
  have htail := successful_fragmentation_tail weight queries boundaries success q b p
    (p / 4) hweight hsuccess hcap
  have hratio : weightedCount weight queries / (q + 1 : ℝ) ≤ p / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < q + 1)).mpr
    nlinarith
  linarith

theorem decoder_probability_constant (n p : ℝ) (hn : 8 ≤ n) (hp : 2 / 3 ≤ p) :
    (7 / 16 : ℝ) ≤ p * (1 - 1 / n) * (3 / 4) := by
  have hn0 : 0 < n := by linarith
  have hinv : 1 / n ≤ (1 / 8 : ℝ) := (div_le_div_iff₀ hn0 (by norm_num)).mpr (by linarith)
  have hfactor : (7 / 8 : ℝ) ≤ 1 - 1 / n := by linarith
  nlinarith [mul_nonneg (show 0 ≤ p - 2 / 3 by linarith)
    (show 0 ≤ 1 - 1 / n by linarith)]

theorem epsilon_frontier_arithmetic (n ε q b : ℝ)
    (hn : 0 < n) (hε : ε ≤ 1 / 128)
    (hledger : (5 / 48 : ℝ) ≤
      ((2 * (1 / n + ε) + 4 * (5 * ε)) * q) / n + 2 * (5 * ε) * (b + 1)) :
    (5 / 192 : ℝ) ≤ (2 / n ^ 2 + 22 * ε / n) * q + 10 * ε * b := by
  have hid : ((2 * (1 / n + ε) + 4 * (5 * ε)) * q) / n +
      2 * (5 * ε) * (b + 1) =
      (2 / n ^ 2 + 22 * ε / n) * q + 10 * ε * b + 10 * ε := by
    field_simp
    ring
  rw [hid] at hledger
  linarith

/-- This derives the query/output frontier from actual weighted events and a
pointwise failure decoder. The continuous collision, query-loss and output-loss
bounds are explicit external hypotheses, not conclusions assumed wholesale. -/
theorem finite_epsilon_query_output_frontier (weight : Outcome → ℝ)
    (queries boundaries : Outcome → ℕ)
    (signal badQuery badOutput failure : Finset Outcome) (n ε : ℝ)
    (hn : 8 ≤ n) (hε : ε ≤ 1 / 128)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hdecoder : ∀ ω ∈ signal, ω ∉ badQuery → ω ∉ badOutput → ω ∈ failure)
    (hsignal : (7 / 16 : ℝ) ≤ eventMass weight signal)
    (hfailure : eventMass weight failure ≤ 1 / 3)
    (hquery : eventMass weight badQuery ≤
      ((2 * (1 / n + ε) + 4 * (5 * ε)) * weightedCount weight queries) / n)
    (houtput : eventMass weight badOutput ≤
      2 * (5 * ε) * (weightedCount weight boundaries + 1)) :
    (5 / 192 : ℝ) ≤ (2 / n ^ 2 + 22 * ε / n) * weightedCount weight queries +
      10 * ε * weightedCount weight boundaries := by
  have hdecomp := failure_mass_after_two_exceptions weight signal badQuery badOutput failure
    hweight hdecoder
  apply epsilon_frontier_arithmetic n ε (weightedCount weight queries)
    (weightedCount weight boundaries) (by linarith) hε
  linarith

end WeightedEvents

section VirtualQueryGeometry

open R4SignedLinear

variable {Agent Coord : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Coord]

noncomputable def outsiders (C : Agent → Coord → ℝ) (q : Agent) : Finset Agent := by
  classical
  exact Finset.univ.filter (fun i => C i ≠ C q)

/-- Agent multiplicity is retained. The easy exceptional geometry is either
at most one outsider, or exactly two outsiders around a strict convex center. -/
def CentralPresentRow (C : Agent → Coord → ℝ) (q : Agent) : Prop :=
  (outsiders C q).card ≤ 1 ∨
    ∃ (p s : Agent) (t : ℝ), p ≠ s ∧ outsiders C q = {p, s} ∧
      0 < t ∧ t < 1 ∧ C q = t • C p + (1 - t) • C s

theorem hard_present_row_has_guards (C : Agent → Coord → ℝ) (totals : Coord → ℝ)
    (hnet : ∀ i, C i ⬝ᵥ totals = 1) (hhard : ∀ q, ¬ CentralPresentRow C q)
    (q : Agent) :
    ∃ p s z, p ≠ s ∧ C q ⬝ᵥ z = 0 ∧ 0 < C p ⬝ᵥ z ∧ 0 < C s ⬝ᵥ z := by
  classical
  have houtside : ∀ i, i ∈ outsiders C q ↔ C i ≠ C q := by simp [outsiders]
  rcases public_coefficient_row_dichotomy C totals q (outsiders C q) houtside hnet with
    hsmall | hcentral | hguards
  · exact False.elim (hhard q (Or.inl hsmall))
  · exact False.elim (hhard q (Or.inr hcentral))
  · exact hguards

/-- Even a new normalized center absent from the public rows has two guards:
all n differences are nonzero, and three cannot all obstruct separation. -/
theorem normalized_virtual_center_has_guards (C : Agent → Coord → ℝ)
    (totals center : Coord → ℝ) (hcard : 3 ≤ Fintype.card Agent)
    (hnet : ∀ i, C i ⬝ᵥ totals = 1) (hcenter : center ⬝ᵥ totals = 1)
    (hhard : ∀ q, ¬ CentralPresentRow C q) :
    ∃ p s z, p ≠ s ∧ center ⬝ᵥ z = 0 ∧ 0 < C p ⬝ᵥ z ∧ 0 < C s ⬝ᵥ z := by
  classical
  by_cases hpresent : ∃ q, C q = center
  · obtain ⟨q, hq⟩ := hpresent
    simpa [hq] using hard_present_row_has_guards C totals hnet hhard q
  · have hnonzero (i : Agent) : C i - center ≠ 0 := by
      intro hz
      exact hpresent ⟨i, sub_eq_zero.mp hz⟩
    have hthree : 2 < (Finset.univ : Finset Agent).card := by
      simpa only [Finset.card_univ] using (show 2 < Fintype.card Agent by omega)
    obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hthree
    rcases three_nonzero_vectors_have_separated_pair (C a - center) (C b - center)
      (C c - center) (hnonzero a) (hnonzero b) (hnonzero c) with
      ⟨z, ha, hb⟩ | ⟨z, ha, hc⟩ | ⟨z, hb, hc⟩
    · exact ⟨a, b, queryProjection center totals z, hab,
        projected_direction_separates center (C a) (C b) totals z
          hcenter (hnet a) (hnet b) ha hb⟩
    · exact ⟨a, c, queryProjection center totals z, hac,
        projected_direction_separates center (C a) (C c) totals z
          hcenter (hnet a) (hnet c) ha hc⟩
    · exact ⟨b, c, queryProjection center totals z, hbc,
        projected_direction_separates center (C b) (C c) totals z
          hcenter (hnet b) (hnet c) hb hc⟩

/-- Every fixed virtual scalar query row admits a kernel direction positive
for two distinct agents when no present row has the easy central geometry.
The virtual row need not itself be a public row or have nonzero total. -/
theorem arbitrary_virtual_query_has_guards (C : Agent → Coord → ℝ)
    (totals queried : Coord → ℝ) (hcard : 3 ≤ Fintype.card Agent)
    (hnet : ∀ i, C i ⬝ᵥ totals = 1) (hhard : ∀ q, ¬ CentralPresentRow C q) :
    ∃ p s z, p ≠ s ∧ queried ⬝ᵥ z = 0 ∧ 0 < C p ⬝ᵥ z ∧ 0 < C s ⬝ᵥ z := by
  classical
  by_cases hzero : queried ⬝ᵥ totals = 0
  · have htwo : 1 < (Finset.univ : Finset Agent).card := by
      simpa using (show 1 < Fintype.card Agent by omega)
    obtain ⟨p, _, s, _, hps⟩ := Finset.one_lt_card.mp htwo
    exact ⟨p, s, totals, hps, hzero, by rw [hnet p]; norm_num, by rw [hnet s]; norm_num⟩
  · let center := (queried ⬝ᵥ totals)⁻¹ • queried
    have hcenter : center ⬝ᵥ totals = 1 := by
      simp [center, smul_dotProduct, hzero]
    obtain ⟨p, s, z, hps, hkernel, hp, hs⟩ :=
      normalized_virtual_center_has_guards C totals center hcard hnet hcenter hhard
    have hquery : queried ⬝ᵥ z = 0 := by
      change (queried ⬝ᵥ totals)⁻¹ • queried ⬝ᵥ z = 0 at hkernel
      rw [smul_dotProduct, smul_eq_mul] at hkernel
      exact (mul_eq_zero.mp hkernel).resolve_left (inv_ne_zero hzero)
    exact ⟨p, s, z, hps, hquery, hp, hs⟩

omit [DecidableEq Agent] in
theorem positive_guard_is_outsider (C : Agent → Coord → ℝ) (q i : Agent)
    (z : Coord → ℝ) (hkernel : C q ⬝ᵥ z = 0) (hpositive : 0 < C i ⬝ᵥ z) :
    i ∈ outsiders C q := by
  classical
  simp only [outsiders, Finset.mem_filter, Finset.mem_univ, true_and]
  intro heq
  rw [heq, hkernel] at hpositive
  exact lt_irrefl _ hpositive

/-- A central present row really obstructs two positive observers on its
kernel. This proves the converse geometric obstruction, retaining clones. -/
theorem central_row_has_no_two_guards (C : Agent → Coord → ℝ) (q : Agent)
    (hcentral : CentralPresentRow C q) :
    ¬ ∃ p s z, p ≠ s ∧ C q ⬝ᵥ z = 0 ∧ 0 < C p ⬝ᵥ z ∧ 0 < C s ⬝ᵥ z := by
  classical
  rintro ⟨p, s, z, hps, hkernel, hp, hs⟩
  have hpo := positive_guard_is_outsider C q p z hkernel hp
  have hso := positive_guard_is_outsider C q s z hkernel hs
  rcases hcentral with hsmall | ⟨a, b, t, _, hset, ht0, ht1, hcenter⟩
  · have htwo := Finset.one_lt_card.mpr ⟨p, hpo, s, hso, hps⟩
    omega
  · have hpindex : p = a ∨ p = b := by simpa [hset] using hpo
    have hsindex : s = a ∨ s = b := by simpa [hset] using hso
    have hcontrad (ha : 0 < C a ⬝ᵥ z) (hb : 0 < C b ⬝ᵥ z) : False := by
      have hpositive : 0 < t * (C a ⬝ᵥ z) + (1 - t) * (C b ⬝ᵥ z) :=
        add_pos (mul_pos ht0 ha) (mul_pos (by linarith) hb)
      rw [hcenter, add_dotProduct, smul_dotProduct, smul_dotProduct,
        smul_eq_mul, smul_eq_mul] at hkernel
      linarith
    rcases hpindex with rfl | rfl <;> rcases hsindex with rfl | rfl
    · exact hps rfl
    · exact hcontrad hp hs
    · exact hcontrad hs hp
    · exact hps rfl

/-- Exact finite geometric characterization. The universal quantifier over
query rows is pointwise algebra and asserts no adaptive-query protocol theorem. -/
theorem all_virtual_guards_iff_hard_geometry (C : Agent → Coord → ℝ)
    (totals : Coord → ℝ) (hcard : 3 ≤ Fintype.card Agent)
    (hnet : ∀ i, C i ⬝ᵥ totals = 1) :
    (∀ queried : Coord → ℝ, ∃ p s z,
      p ≠ s ∧ queried ⬝ᵥ z = 0 ∧ 0 < C p ⬝ᵥ z ∧ 0 < C s ⬝ᵥ z) ↔
      ∀ q, ¬ CentralPresentRow C q := by
  constructor
  · intro hguards q hcentral
    exact central_row_has_no_two_guards C q hcentral (hguards (C q))
  · intro hhard queried
    exact arbitrary_virtual_query_has_guards C totals queried hcard hnet hhard

end VirtualQueryGeometry

end EnvyFreeResearch.R6Lower

#print axioms EnvyFreeResearch.R6Lower.all_prefixes_determined
#print axioms EnvyFreeResearch.R6Lower.all_bundles_determined
#print axioms EnvyFreeResearch.R6Lower.verified_comparisons_transfer
#print axioms EnvyFreeResearch.R6Lower.prefix_query_count
#print axioms EnvyFreeResearch.R6Lower.capped_verifier_query_bound
#print axioms EnvyFreeResearch.R6Lower.weightedCount_nonnegative
#print axioms EnvyFreeResearch.R6Lower.query_tail_markov
#print axioms EnvyFreeResearch.R6Lower.successful_fragmentation_tail
#print axioms EnvyFreeResearch.R6Lower.half_success_fragmentation_tail
#print axioms EnvyFreeResearch.R6Lower.decoder_probability_constant
#print axioms EnvyFreeResearch.R6Lower.epsilon_frontier_arithmetic
#print axioms EnvyFreeResearch.R6Lower.finite_epsilon_query_output_frontier
#print axioms EnvyFreeResearch.R6Lower.hard_present_row_has_guards
#print axioms EnvyFreeResearch.R6Lower.normalized_virtual_center_has_guards
#print axioms EnvyFreeResearch.R6Lower.arbitrary_virtual_query_has_guards
#print axioms EnvyFreeResearch.R6Lower.positive_guard_is_outsider
#print axioms EnvyFreeResearch.R6Lower.central_row_has_no_two_guards
#print axioms EnvyFreeResearch.R6Lower.all_virtual_guards_iff_hard_geometry
