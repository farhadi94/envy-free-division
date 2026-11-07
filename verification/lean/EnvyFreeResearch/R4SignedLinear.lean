import EnvyFreeResearch.Signed
import EnvyFreeResearch.R2Variation
import EnvyFreeResearch.R3PrioritySelector

/-!
# Round 4: finite certificates for public signed coefficient models

These statements concern finite coefficient vectors, utility tables, and
ownership maps. The unknown basis measures may be signed. Continuous roots,
measure realization, query transcripts, and probability are separate
handwritten obligations. No oracle or complete-protocol axiom is used here.
-/

namespace EnvyFreeResearch.R4SignedLinear

open scoped BigOperators

/-- Project a direction into the queried row's kernel using public totals. -/
noncomputable def queryProjection {Coord : Type*} [Fintype Coord]
    (queried totals direction : Coord → ℝ) : Coord → ℝ :=
  direction - (queried ⬝ᵥ direction) • totals

theorem query_projection_annihilates {Coord : Type*} [Fintype Coord]
    (queried totals direction : Coord → ℝ) (hnet : queried ⬝ᵥ totals = 1) :
    queried ⬝ᵥ queryProjection queried totals direction = 0 := by
  simp [queryProjection, dotProduct_sub, dotProduct_smul, hnet]

theorem projected_row_is_difference {Coord : Type*} [Fintype Coord]
    (row queried totals direction : Coord → ℝ)
    (hnet : row ⬝ᵥ totals = 1) :
    row ⬝ᵥ queryProjection queried totals direction =
      (row - queried) ⬝ᵥ direction := by
  simp [queryProjection, dotProduct_sub, dotProduct_smul, sub_dotProduct, hnet]

theorem projection_preserves_difference {Coord : Type*} [Fintype Coord]
    (row queried totals direction : Coord → ℝ)
    (hrow : row ⬝ᵥ totals = 1) (hqueried : queried ⬝ᵥ totals = 1) :
    (row - queried) ⬝ᵥ queryProjection queried totals direction =
      (row - queried) ⬝ᵥ direction := by
  simp [queryProjection, dotProduct_sub, dotProduct_smul, sub_dotProduct, hrow, hqueried]

theorem projected_direction_separates {Coord : Type*} [Fintype Coord]
    (queried first second totals direction : Coord → ℝ)
    (hq : queried ⬝ᵥ totals = 1) (hp : first ⬝ᵥ totals = 1)
    (hs : second ⬝ᵥ totals = 1)
    (hfirst : 0 < (first - queried) ⬝ᵥ direction)
    (hsecond : 0 < (second - queried) ⬝ᵥ direction) :
    queried ⬝ᵥ queryProjection queried totals direction = 0 ∧
      0 < first ⬝ᵥ queryProjection queried totals direction ∧
      0 < second ⬝ᵥ queryProjection queried totals direction := by
  refine ⟨query_projection_annihilates queried totals direction hq, ?_, ?_⟩
  · simpa only [projected_row_is_difference first queried totals direction hp] using hfirst
  · simpa only [projected_row_is_difference second queried totals direction hs] using hsecond

theorem coefficient_pulse_value {Coord : Type*} [Fintype Coord]
    (row base direction : Coord → ℝ) (mass : ℝ) :
    row ⬝ᵥ (base + mass • direction) = row ⬝ᵥ base + mass * (row ⬝ᵥ direction) := by
  simp [dotProduct_add, dotProduct_smul]

theorem pulse_preserves_queried_row {Coord : Type*} [Fintype Coord]
    (queried base direction : Coord → ℝ) (mass : ℝ)
    (hkernel : queried ⬝ᵥ direction = 0) :
    queried ⬝ᵥ (base + mass • direction) = queried ⬝ᵥ base := by
  simp [hkernel]

/-- All public linear relations are inherited by every coefficient-generated
atom value, including before and after a common basis pulse. -/
theorem coefficient_relation_preserved {Agent Coord : Type*}
    [Fintype Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (weights : Agent → ℝ) (basis : Coord → ℝ)
    (hrelation : ∀ k, ∑ i, weights i * C i k = 0) :
    ∑ i, weights i * (C i ⬝ᵥ basis) = 0 := by
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ k, ∑ i, weights i * (C i k * basis k) =
        ∑ k, (∑ i, weights i * C i k) * basis k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp [hrelation]

theorem basis_split_conserves_every_row {Coord : Type*} [Fintype Coord]
    (row parent left : Coord → ℝ) :
    row ⬝ᵥ left + row ⬝ᵥ (parent - left) = row ⬝ᵥ parent := by
  rw [dotProduct_sub]
  ring

/-- A zero-total basis perturbation has zero total in every agent row. -/
theorem coefficient_row_sum_zero {Agent Coord : Type*}
    [Fintype Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (Z : Coord → Agent → ℝ)
    (hzero : ∀ k, ∑ j, Z k j = 0) (i : Agent) :
    ∑ j, C i ⬝ᵥ (fun k => Z k j) = 0 := by
  simp only [dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hzero, mul_zero]
  exact Finset.sum_const_zero

/-- A row with zero sum and zero comparison against its own column is zero.
The available observer supplies the nonempty finite index type. -/
theorem zero_comparisons_force_zero_row {Agent : Type*} [Fintype Agent]
    (row : Agent → ℝ) (observer : Agent)
    (hzero : ∑ j, row j = 0)
    (hcontrast : ∀ j, row j - row observer = 0) :
    ∀ j, row j = 0 := by
  have hequal : ∀ j, row j = row observer := fun j => sub_eq_zero.mp (hcontrast j)
  have hn : (Fintype.card Agent : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨observer⟩))
  have hsum : (Fintype.card Agent : ℝ) * row observer = 0 := by
    simpa [hequal] using hzero
  have hown : row observer = 0 := (mul_eq_zero.mp hsum).resolve_left hn
  intro j
  rw [hequal j, hown]

/-- Full-column injectivity and zero basis row sums make the complete family
of envy comparisons faithful: vanishing comparisons force `Z = 0`. -/
theorem contrast_kernel_is_zero {Agent Coord : Type*}
    [Fintype Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (Z : Coord → Agent → ℝ)
    (hinjective : Function.Injective (fun z : Coord → ℝ => fun i => C i ⬝ᵥ z))
    (hzero : ∀ k, ∑ j, Z k j = 0)
    (hcontrast : ∀ i j,
      C i ⬝ᵥ (fun k => Z k j) - C i ⬝ᵥ (fun k => Z k i) = 0) :
    Z = 0 := by
  have hvalues : ∀ i j, C i ⬝ᵥ (fun k => Z k j) = 0 := by
    intro i
    exact zero_comparisons_force_zero_row
      (fun j => C i ⬝ᵥ (fun k => Z k j)) i
      (coefficient_row_sum_zero C Z hzero i) (hcontrast i)
  funext k j
  have hcol : (fun l => Z l j) = 0 := by
    apply hinjective
    funext i
    simpa using hvalues i j
  exact congrFun hcol k

theorem nonzero_perturbation_changes_comparison {Agent Coord : Type*}
    [Fintype Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (Z : Coord → Agent → ℝ)
    (hinjective : Function.Injective (fun z : Coord → ℝ => fun i => C i ⬝ᵥ z))
    (hzero : ∀ k, ∑ j, Z k j = 0) (hZ : Z ≠ 0) :
    ∃ i j, C i ⬝ᵥ (fun k => Z k j) - C i ⬝ᵥ (fun k => Z k i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hZ (contrast_kernel_is_zero C Z hinjective hzero h)

theorem nonzero_comparison_can_be_oriented (comparison : ℝ) (h : comparison ≠ 0) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧ 0 < sign * comparison := by
  by_cases hp : 0 < comparison
  · exact ⟨1, Or.inl rfl, by simpa using hp⟩
  · have hn : comparison < 0 := lt_of_le_of_ne (le_of_not_gt hp) h
    exact ⟨-1, Or.inr rfl, by simpa using neg_pos.mpr hn⟩

/-- Equal central values reverse the two outsiders' rankings. -/
theorem convex_equal_values_reverse (weight firstA firstB secondA secondB center : ℝ)
    (hweight : 0 < weight) (hweight1 : weight < 1)
    (hA : weight * firstA + (1 - weight) * secondA = center)
    (hB : weight * firstB + (1 - weight) * secondB = center)
    (hfirst : firstA ≤ firstB) : secondB ≤ secondA := by
  have hscaled := mul_le_mul_of_nonneg_left hfirst (le_of_lt hweight)
  by_contra hsecond
  have hpositive : 0 < (1 - weight) * (secondB - secondA) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- A finite list with at least two positions has distinct maximum/minimum
positions. If all values tie, two preselected distinct positions suffice. -/
theorem distinct_max_min {Piece : Type*} [Fintype Piece] [DecidableEq Piece]
    (value : Piece → ℝ) (first second : Piece) (hdistinct : first ≠ second) :
    ∃ best worst, best ≠ worst ∧
      (∀ j, value j ≤ value best) ∧ (∀ j, value worst ≤ value j) := by
  obtain ⟨best, _, hbest⟩ := Finset.exists_max_image Finset.univ value
    ⟨first, Finset.mem_univ first⟩
  obtain ⟨worst, _, hworst⟩ := Finset.exists_min_image Finset.univ value
    ⟨first, Finset.mem_univ first⟩
  by_cases hbw : best = worst
  · have hall : ∀ j, value j = value best := by
      intro j
      exact le_antisymm (hbest j (Finset.mem_univ j))
        (by simpa only [← hbw] using hworst j (Finset.mem_univ j))
    exact ⟨first, second, hdistinct,
      fun j => by rw [hall j, hall first], fun j => by rw [hall second, hall j]⟩
  · exact ⟨best, worst, hbw, fun j => hbest j (Finset.mem_univ j),
      fun j => hworst j (Finset.mem_univ j)⟩

/-- Any two distinct agents can be sent to two distinct pieces by an explicit
composition of swaps, leaving a complete bijective assignment. -/
theorem assignment_for_two_choices {Agent : Type*} [DecidableEq Agent]
    (first second best worst : Agent) (hag : first ≠ second) (hp : best ≠ worst) :
    ∃ assignment : Agent ≃ Agent, assignment first = best ∧ assignment second = worst := by
  let step : Agent ≃ Agent := Equiv.swap first best
  have hstep : step first = best := Equiv.swap_apply_left first best
  have hnotbest : step second ≠ best := by
    intro h
    have heq : second = first := step.injective (h.trans hstep.symm)
    exact hag heq.symm
  refine ⟨step.trans (Equiv.swap (step second) worst), ?_, ?_⟩
  · change Equiv.swap (step second) worst (step first) = best
    rw [hstep]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hnotbest) hp
  · exact Equiv.swap_apply_left (step second) worst

/-- Utility-table certificate for two opposite outsiders and indifferent
central agents, including complete assignment and tied extrema. -/
theorem opposite_outsiders_complete_EF {Agent : Type*}
    [Fintype Agent] [DecidableEq Agent]
    (v : Agent → Agent → ℝ) (first second : Agent)
    (weight center : ℝ) (hdistinct : first ≠ second)
    (hweight : 0 < weight) (hweight1 : weight < 1)
    (hcentral : ∀ i, i ≠ first → i ≠ second → ∀ piece, v i piece = center)
    (hrelation : ∀ piece, weight * v first piece + (1 - weight) * v second piece = center) :
    ∃ assignment : Agent ≃ Agent, Signed.EnvyFree (fun i j => v i (assignment j)) := by
  obtain ⟨best, worst, hbw, hbest, hworst⟩ :=
    distinct_max_min (v first) first second hdistinct
  obtain ⟨assignment, hfirst, hsecond⟩ :=
    assignment_for_two_choices first second best worst hdistinct hbw
  refine ⟨assignment, ?_⟩
  intro i j
  change v i (assignment j) ≤ v i (assignment i)
  by_cases hi : i = first
  · subst i
    rw [hfirst]
    exact hbest (assignment j)
  · by_cases hs : i = second
    · subst i
      rw [hsecond]
      exact convex_equal_values_reverse weight (v first worst) (v first (assignment j))
        (v second worst) (v second (assignment j)) center hweight hweight1
        (hrelation worst) (hrelation (assignment j)) (hworst (assignment j))
    · rw [hcentral i hi hs (assignment j), hcentral i hi hs (assignment i)]

theorem convex_coefficient_piece_relation {Coord : Type*} [Fintype Coord]
    (central first second piece : Coord → ℝ) (weight : ℝ)
    (hrelation : central = weight • first + (1 - weight) • second) :
    central ⬝ᵥ piece = weight * (first ⬝ᵥ piece) + (1 - weight) * (second ⬝ᵥ piece) := by
  simp [hrelation, add_dotProduct, smul_dotProduct]

/-- The finite easy-side protocol for public coefficients: equal central-row
pieces and two singleton outsiders on opposite rays admit a complete EF
assignment. No signs are imposed on any piece or basis coordinate. -/
theorem central_opposite_coefficients_complete_EF {Agent Coord : Type*}
    [Fintype Agent] [DecidableEq Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (pieces : Agent → Coord → ℝ)
    (central first second : Agent) (weight equalValue : ℝ)
    (hdistinct : first ≠ second) (hweight : 0 < weight) (hweight1 : weight < 1)
    (hrelation : C central = weight • C first + (1 - weight) • C second)
    (hclones : ∀ i, i ≠ first → i ≠ second → C i = C central)
    (hequal : ∀ piece, C central ⬝ᵥ pieces piece = equalValue) :
    ∃ assignment : Agent ≃ Agent,
      Signed.EnvyFree (fun i j => C i ⬝ᵥ pieces (assignment j)) := by
  apply opposite_outsiders_complete_EF (fun i piece => C i ⬝ᵥ pieces piece)
    first second weight equalValue hdistinct hweight hweight1
  · intro i hi hs piece
    rw [hclones i hi hs, hequal piece]
  · intro piece
    rw [← convex_coefficient_piece_relation (C central) (C first) (C second)
      (pieces piece) weight hrelation, hequal piece]

/-- One common integer amplitude can clear both forcing thresholds and retain
every recorded nonzero affine mismatch. -/
theorem integer_pulse_meets_guards_and_exclusions {Index : Type*}
    (s : Finset Index) (offset slope : Index → ℝ)
    (hoffset : ∀ j ∈ s, offset j ≠ 0)
    (baseFirst baseSecond directionFirst directionSecond guardFirst guardSecond : ℝ)
    (hfirst : 0 < directionFirst) (hsecond : 0 < directionSecond) :
    ∃ mass : ℕ,
      guardFirst ≤ baseFirst + (mass : ℝ) * directionFirst ∧
      guardSecond ≤ baseSecond + (mass : ℝ) * directionSecond ∧
      ∀ j ∈ s, offset j + slope j * (mass : ℝ) ≠ 0 := by
  obtain ⟨mass, hmass, hexclude⟩ := RealRandomMixedFinite.large_integer_avoids_affine_zeros
    s offset slope hoffset
    (max ((guardFirst - baseFirst) / directionFirst)
      ((guardSecond - baseSecond) / directionSecond))
  have hmfirst : (guardFirst - baseFirst) / directionFirst < (mass : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hmass
  have hmsecond : (guardSecond - baseSecond) / directionSecond < (mass : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hmass
  have hprodFirst := (div_lt_iff₀ hfirst).mp hmfirst
  have hprodSecond := (div_lt_iff₀ hsecond).mp hmsecond
  exact ⟨mass, by linarith, by linarith, hexclude⟩

/-- Value of an old bundle, with one distinguished parent atom. -/
def oldValue {Atom Agent : Type*} [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Atom → ℝ) (owner : Atom → Agent)
    (parentOwner : Agent) (parent : ℝ) (recipient : Agent) : ℝ :=
  R2Variation.outsideValue atoms outside owner recipient +
    if recipient = parentOwner then parent else 0

/-- Actual value after the distinguished parent is replaced by two children. -/
def splitValue {Atom Agent : Type*} [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Atom → ℝ) (owner : Atom → Agent)
    (leftOwner rightOwner : Agent) (parent child : ℝ) (recipient : Agent) : ℝ :=
  R2Variation.outsideValue atoms outside owner recipient +
    (if recipient = leftOwner then child else 0) +
    (if recipient = rightOwner then parent - child else 0)

theorem splitValue_coassigned {Atom Agent : Type*} [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Atom → ℝ) (owner : Atom → Agent)
    (jointOwner : Agent) (parent child : ℝ) (recipient : Agent) :
    splitValue atoms outside owner jointOwner jointOwner parent child recipient =
      oldValue atoms outside owner jointOwner parent recipient := by
  by_cases h : recipient = jointOwner
  · simp only [splitValue, oldValue, h, ↓reduceIte]
    ring
  · simp [splitValue, oldValue, h]

/-- A left child at least outside variation plus the net total forces a gap
against every nonowner when its sibling has a different owner. -/
theorem guarded_split_gap {Atom Agent : Type*} [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Atom → ℝ) (owner : Atom → Agent)
    (leftOwner rightOwner observer : Agent) (parent child total : ℝ)
    (hnet : parent + ∑ a ∈ atoms, outside a = total)
    (hguard : (∑ a ∈ atoms, |outside a|) + total ≤ child)
    (hseparated : leftOwner ≠ rightOwner) (hnotleft : observer ≠ leftOwner) :
    total ≤ splitValue atoms outside owner leftOwner rightOwner parent child leftOwner -
      splitValue atoms outside owner leftOwner rightOwner parent child observer := by
  have hconstraint := R2Variation.outside_mass_constraint atoms outside parent total hnet
  have hparent : parent - total ≤ ∑ a ∈ atoms, |outside a| := by
    have h := (abs_le.mp hconstraint).1
    linarith
  have hdifference := R2Variation.outside_difference_lower_bound
    atoms outside owner leftOwner observer
  by_cases hright : observer = rightOwner
  · have h := (RealRandomMixedFinite.forced_split_with_slack parent
      (∑ a ∈ atoms, |outside a|) total child
      (R2Variation.outsideValue atoms outside owner leftOwner)
      (R2Variation.outsideValue atoms outside owner observer) true
      hparent hguard hdifference).2
    simp [splitValue, hseparated, Ne.symm hseparated, hright] at h ⊢
    linarith
  · have h := (RealRandomMixedFinite.forced_split_with_slack parent
      (∑ a ∈ atoms, |outside a|) total child
      (R2Variation.outsideValue atoms outside owner leftOwner)
      (R2Variation.outsideValue atoms outside owner observer) false
      hparent hguard hdifference).2
    simp [splitValue, hseparated, hnotleft, hright] at h ⊢
    linarith

theorem two_guarded_observers_gap {Atom Agent : Type*} [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Agent → Atom → ℝ) (owner : Atom → Agent)
    (parent child : Agent → ℝ) (total : ℝ)
    (leftOwner rightOwner first second : Agent)
    (hseparated : leftOwner ≠ rightOwner) (hdistinct : first ≠ second)
    (hnetFirst : parent first + ∑ a ∈ atoms, outside first a = total)
    (hnetSecond : parent second + ∑ a ∈ atoms, outside second a = total)
    (hguardFirst : (∑ a ∈ atoms, |outside first a|) + total ≤ child first)
    (hguardSecond : (∑ a ∈ atoms, |outside second a|) + total ≤ child second) :
    ∃ i, (i = first ∨ i = second) ∧
      total ≤ splitValue atoms (outside i) owner leftOwner rightOwner (parent i) (child i) leftOwner -
        splitValue atoms (outside i) owner leftOwner rightOwner (parent i) (child i) i := by
  by_cases hfirst : first = leftOwner
  · have hsecond : second ≠ leftOwner := by
      intro h
      exact hdistinct (hfirst.trans h.symm)
    exact ⟨second, Or.inr rfl, guarded_split_gap atoms (outside second) owner
      leftOwner rightOwner second (parent second) (child second) total
      hnetSecond hguardSecond hseparated hsecond⟩
  · exact ⟨first, Or.inl rfl, guarded_split_gap atoms (outside first) owner
      leftOwner rightOwner first (parent first) (child first) total
      hnetFirst hguardFirst hseparated hfirst⟩

/-- The finite all-ownership extension: old obstructions survive coassignment,
and two guarded observers certify every separated placement. -/
theorem guarded_refinement_preserves_obstruction {Atom Agent : Type*}
    [DecidableEq Agent]
    (atoms : Finset Atom) (outside : Agent → Atom → ℝ) (owner : Atom → Agent)
    (parent child : Agent → ℝ) (total : ℝ) (first second : Agent)
    (hdistinct : first ≠ second)
    (hnet : ∀ i, parent i + ∑ a ∈ atoms, outside i a = total)
    (hguardFirst : (∑ a ∈ atoms, |outside first a|) + total ≤ child first)
    (hguardSecond : (∑ a ∈ atoms, |outside second a|) + total ≤ child second)
    (hprior : ∀ jointOwner, ∃ i j, total ≤
      oldValue atoms (outside i) owner jointOwner (parent i) j -
        oldValue atoms (outside i) owner jointOwner (parent i) i)
    (leftOwner rightOwner : Agent) :
    ∃ i j, total ≤
      splitValue atoms (outside i) owner leftOwner rightOwner (parent i) (child i) j -
        splitValue atoms (outside i) owner leftOwner rightOwner (parent i) (child i) i := by
  by_cases hsame : leftOwner = rightOwner
  · subst rightOwner
    obtain ⟨i, j, hgap⟩ := hprior leftOwner
    exact ⟨i, j, by simpa only [splitValue_coassigned] using hgap⟩
  · obtain ⟨i, _, hgap⟩ := two_guarded_observers_gap atoms outside owner parent child total
      leftOwner rightOwner first second hsame hdistinct (hnet first) (hnet second)
      hguardFirst hguardSecond
    exact ⟨i, leftOwner, hgap⟩

/-- The actual utility row induced by a common vector pulse in basis space. -/
noncomputable def coefficientSplitValue {Atom Agent Coord : Type*}
    [DecidableEq Agent] [Fintype Coord]
    (atoms : Finset Atom) (C : Agent → Coord → ℝ) (outside : Coord → Atom → ℝ)
    (parent base direction : Coord → ℝ) (mass : ℝ) (owner : Atom → Agent)
    (leftOwner rightOwner observer recipient : Agent) : ℝ :=
  splitValue atoms (fun a => C observer ⬝ᵥ (fun k => outside k a)) owner
    leftOwner rightOwner (C observer ⬝ᵥ parent)
    (C observer ⬝ᵥ (base + mass • direction)) recipient

/-- One common integer pulse simultaneously preserves the queried row, avoids
all finitely many priority exclusions, and preserves the obstruction for
EVERY ownership map. Its amplitude is chosen before any ownership map. -/
theorem correlated_pulse_preserves_obstruction {Atom Agent Coord Index : Type*}
    [DecidableEq Agent] [Fintype Coord]
    (atoms : Finset Atom) (C : Agent → Coord → ℝ) (outside : Coord → Atom → ℝ)
    (parent base direction : Coord → ℝ) (total : ℝ) (queried first second : Agent)
    (excluded : Finset Index) (offset slope : Index → ℝ)
    (hoffset : ∀ j ∈ excluded, offset j ≠ 0)
    (hkernel : C queried ⬝ᵥ direction = 0)
    (hfirst : 0 < C first ⬝ᵥ direction) (hsecond : 0 < C second ⬝ᵥ direction)
    (hdistinct : first ≠ second)
    (hnet : ∀ i, C i ⬝ᵥ parent + ∑ a ∈ atoms, C i ⬝ᵥ (fun k => outside k a) = total)
    (hprior : ∀ (owner : Atom → Agent) jointOwner, ∃ i j, total ≤
      oldValue atoms (fun a => C i ⬝ᵥ (fun k => outside k a)) owner jointOwner
        (C i ⬝ᵥ parent) j -
      oldValue atoms (fun a => C i ⬝ᵥ (fun k => outside k a)) owner jointOwner
        (C i ⬝ᵥ parent) i) :
    ∃ mass : ℕ,
      C queried ⬝ᵥ (base + (mass : ℝ) • direction) = C queried ⬝ᵥ base ∧
      (∀ j ∈ excluded, offset j + slope j * (mass : ℝ) ≠ 0) ∧
      ∀ (owner : Atom → Agent) leftOwner rightOwner, ∃ i j, total ≤
        coefficientSplitValue atoms C outside parent base direction (mass : ℝ) owner
          leftOwner rightOwner i j -
        coefficientSplitValue atoms C outside parent base direction (mass : ℝ) owner
          leftOwner rightOwner i i := by
  obtain ⟨mass, hguardFirst, hguardSecond, hexclude⟩ :=
    integer_pulse_meets_guards_and_exclusions excluded offset slope hoffset
      (C first ⬝ᵥ base) (C second ⬝ᵥ base)
      (C first ⬝ᵥ direction) (C second ⬝ᵥ direction)
      ((∑ a ∈ atoms, |C first ⬝ᵥ (fun k => outside k a)|) + total)
      ((∑ a ∈ atoms, |C second ⬝ᵥ (fun k => outside k a)|) + total) hfirst hsecond
  refine ⟨mass, pulse_preserves_queried_row (C queried) base direction (mass : ℝ) hkernel,
    hexclude, ?_⟩
  intro owner leftOwner rightOwner
  apply guarded_refinement_preserves_obstruction atoms
    (fun i a => C i ⬝ᵥ (fun k => outside k a)) owner
    (fun i => C i ⬝ᵥ parent) (fun i => C i ⬝ᵥ (base + (mass : ℝ) • direction))
    total first second hdistinct hnet
  · simpa only [coefficient_pulse_value] using hguardFirst
  · simpa only [coefficient_pulse_value] using hguardSecond
  · exact hprior owner

/-- Negative scalar multiples are the only obstruction to a common strictly
positive linear functional for two nonzero finite real vectors. -/
def OppositeRays {Coord : Type*} (first second : Coord → ℝ) : Prop :=
  ∃ scalar : ℝ, scalar < 0 ∧ second = scalar • first

theorem dot_self_positive {Coord : Type*} [Fintype Coord]
    (v : Coord → ℝ) (hnonzero : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hnonneg : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
  have hne : v ⬝ᵥ v ≠ 0 := by
    intro hzero
    apply hnonzero
    have h := (Finset.sum_mul_self_eq_zero_iff Finset.univ v).mp hzero
    funext k
    exact h k (Finset.mem_univ k)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem gram_residual_identity {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) :
    ((second ⬝ᵥ second) • first - (first ⬝ᵥ second) • second) ⬝ᵥ
      ((second ⬝ᵥ second) • first - (first ⬝ᵥ second) • second) =
    (second ⬝ᵥ second) *
      ((first ⬝ᵥ first) * (second ⬝ᵥ second) - (first ⬝ᵥ second) ^ 2) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm second first]
  ring

/-- A direct finite Gram-residual proof of the strict inequality needed by
the separator, with no separation theorem postulated as an axiom. -/
theorem negative_inner_strict_gram {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hsecond : second ≠ 0)
    (hinner : first ⬝ᵥ second < 0) (hopposite : ¬ OppositeRays first second) :
    (first ⬝ᵥ second) ^ 2 < (first ⬝ᵥ first) * (second ⬝ᵥ second) := by
  have hnorm := dot_self_positive second hsecond
  have hresidual : (second ⬝ᵥ second) • first - (first ⬝ᵥ second) • second ≠ 0 := by
    intro hzero
    apply hopposite
    refine ⟨(second ⬝ᵥ second) / (first ⬝ᵥ second),
      div_neg_of_pos_of_neg hnorm hinner, ?_⟩
    funext k
    have hk := congrFun hzero k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    change second k = ((second ⬝ᵥ second) / (first ⬝ᵥ second)) * first k
    field_simp [ne_of_lt hinner]
    linarith
  have hpositive := dot_self_positive _ hresidual
  rw [gram_residual_identity] at hpositive
  by_contra h
  have hnonpos : (first ⬝ᵥ first) * (second ⬝ᵥ second) - (first ⬝ᵥ second) ^ 2 ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt h)
  have hproduct := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hnorm) hnonpos
  linarith

theorem positive_separator_of_nonnegative_inner {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hinner : 0 ≤ first ⬝ᵥ second) :
    0 < first ⬝ᵥ (first + second) ∧ 0 < second ⬝ᵥ (first + second) := by
  have hp := dot_self_positive first hfirst
  have hs := dot_self_positive second hsecond
  rw [dotProduct_add, dotProduct_add, dotProduct_comm second first]
  constructor <;> linarith

/-- The negative-inner-product branch uses an explicit arithmetic midpoint
between two rational expressions. Thus the displayed construction is rational
whenever the input vectors are rational, although this theorem is over reals. -/
theorem positive_separator_of_negative_inner {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hinner : first ⬝ᵥ second < 0) (hopposite : ¬ OppositeRays first second) :
    ∃ scale : ℝ, 0 < first ⬝ᵥ (first + scale • second) ∧
      0 < second ⬝ᵥ (first + scale • second) := by
  let A := first ⬝ᵥ first
  let B := second ⬝ᵥ second
  let D := first ⬝ᵥ second
  have hA : 0 < A := dot_self_positive first hfirst
  have hB : 0 < B := dot_self_positive second hsecond
  have hD : D < 0 := hinner
  have hgram : D ^ 2 < A * B := negative_inner_strict_gram first second hsecond hinner hopposite
  have hinterval : (-D) / B < A / (-D) := by
    apply (div_lt_div_iff₀ hB (neg_pos.mpr hD)).mpr
    nlinarith
  let scale := (((-D) / B) + A / (-D)) / 2
  have hlo : (-D) / B < scale := by dsimp [scale]; linarith
  have hhi : scale < A / (-D) := by dsimp [scale]; linarith
  have hleft := (lt_div_iff₀ (neg_pos.mpr hD)).mp hhi
  have hright := (div_lt_iff₀ hB).mp hlo
  refine ⟨scale, ?_, ?_⟩
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    change 0 < A + scale * D
    nlinarith
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm second first]
    change 0 < D + scale * B
    linarith

theorem two_nonopposite_vectors_have_separator {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hopposite : ¬ OppositeRays first second) :
    ∃ direction : Coord → ℝ, 0 < first ⬝ᵥ direction ∧ 0 < second ⬝ᵥ direction := by
  by_cases hinner : 0 ≤ first ⬝ᵥ second
  · exact ⟨first + second,
      positive_separator_of_nonnegative_inner first second hfirst hsecond hinner⟩
  · obtain ⟨scale, hp, hs⟩ := positive_separator_of_negative_inner first second hfirst hsecond
      (lt_of_not_ge hinner) hopposite
    exact ⟨first + scale • second, hp, hs⟩

theorem opposite_vectors_have_no_separator {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hopposite : OppositeRays first second) :
    ¬ ∃ direction : Coord → ℝ, 0 < first ⬝ᵥ direction ∧ 0 < second ⬝ᵥ direction := by
  obtain ⟨scalar, hscalar, hsecond⟩ := hopposite
  rintro ⟨direction, hfirst, hpositive⟩
  rw [hsecond, smul_dotProduct, smul_eq_mul] at hpositive
  have hnegative := mul_neg_of_neg_of_pos hscalar hfirst
  linarith

theorem separator_iff_not_opposite {Coord : Type*} [Fintype Coord]
    (first second : Coord → ℝ) (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    (∃ direction : Coord → ℝ, 0 < first ⬝ᵥ direction ∧ 0 < second ⬝ᵥ direction) ↔
      ¬ OppositeRays first second := by
  constructor
  · intro hsep hopposite
    exact opposite_vectors_have_no_separator first second hopposite hsep
  · exact two_nonopposite_vectors_have_separator first second hfirst hsecond

theorem three_nonzero_vectors_have_separated_pair {Coord : Type*} [Fintype Coord]
    (first second third : Coord → ℝ)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0) :
    (∃ direction, 0 < first ⬝ᵥ direction ∧ 0 < second ⬝ᵥ direction) ∨
    (∃ direction, 0 < first ⬝ᵥ direction ∧ 0 < third ⬝ᵥ direction) ∨
    (∃ direction, 0 < second ⬝ᵥ direction ∧ 0 < third ⬝ᵥ direction) := by
  by_cases h12 : OppositeRays first second
  · by_cases h13 : OppositeRays first third
    · obtain ⟨c, hc, hs⟩ := h12
      obtain ⟨d, hd, ht⟩ := h13
      have hnorm := dot_self_positive first hfirst
      refine Or.inr (Or.inr ⟨-first, ?_, ?_⟩)
      · rw [hs, smul_dotProduct, dotProduct_neg, smul_eq_mul]
        exact mul_pos_of_neg_of_neg hc (neg_neg_of_pos hnorm)
      · rw [ht, smul_dotProduct, dotProduct_neg, smul_eq_mul]
        exact mul_pos_of_neg_of_neg hd (neg_neg_of_pos hnorm)
    · exact Or.inr (Or.inl (two_nonopposite_vectors_have_separator first third hfirst hthird h13))
  · exact Or.inl (two_nonopposite_vectors_have_separator first second hfirst hsecond h12)

/-- The finite outsider geometry is exhaustive: at most one outsider, exactly
two opposite outsiders, or a distinct pair with a positive separator. Agent
multiplicity is retained because the finite set indexes agents, not vectors. -/
theorem finite_outsider_geometry {Agent Coord : Type*}
    [DecidableEq Agent] [Fintype Coord]
    (outsiders : Finset Agent) (difference : Agent → Coord → ℝ)
    (hnonzero : ∀ i ∈ outsiders, difference i ≠ 0) :
    outsiders.card ≤ 1 ∨
    (∃ first second, first ∈ outsiders ∧ second ∈ outsiders ∧ first ≠ second ∧
      outsiders = {first, second} ∧ OppositeRays (difference first) (difference second)) ∨
    ∃ first second direction, first ∈ outsiders ∧ second ∈ outsiders ∧ first ≠ second ∧
      0 < difference first ⬝ᵥ direction ∧ 0 < difference second ⬝ᵥ direction := by
  by_cases hsmall : outsiders.card ≤ 1
  · exact Or.inl hsmall
  · by_cases hlarge : 2 < outsiders.card
    · obtain ⟨first, second, third, hf, hs, ht, hfs, hft, hst⟩ :=
        Finset.two_lt_card_iff.mp hlarge
      rcases three_nonzero_vectors_have_separated_pair (difference first) (difference second)
        (difference third) (hnonzero first hf) (hnonzero second hs) (hnonzero third ht) with
        ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz3⟩ | ⟨z, hz2, hz3⟩
      · exact Or.inr (Or.inr ⟨first, second, z, hf, hs, hfs, hz1, hz2⟩)
      · exact Or.inr (Or.inr ⟨first, third, z, hf, ht, hft, hz1, hz3⟩)
      · exact Or.inr (Or.inr ⟨second, third, z, hs, ht, hst, hz2, hz3⟩)
    · obtain ⟨first, hf, second, hs, hfs⟩ := Finset.one_lt_card.mp (lt_of_not_ge hsmall)
      by_cases hopposite : OppositeRays (difference first) (difference second)
      · have hsubset : ({first, second} : Finset Agent) ⊆ outsiders := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> assumption
        have hcard : outsiders.card ≤ ({first, second} : Finset Agent).card := by
          simp only [Finset.card_pair hfs]
          exact le_of_not_gt hlarge
        exact Or.inr (Or.inl ⟨first, second, hf, hs, hfs,
          (Finset.eq_of_subset_of_card_le hsubset hcard).symm, hopposite⟩)
      · obtain ⟨z, hz1, hz2⟩ := two_nonopposite_vectors_have_separator
          (difference first) (difference second) (hnonzero first hf) (hnonzero second hs) hopposite
        exact Or.inr (Or.inr ⟨first, second, z, hf, hs, hfs, hz1, hz2⟩)

/-- Opposite differences give the strict convex identity used by the easy
protocol, with an explicit coefficient in `(0,1)`. -/
theorem opposite_differences_give_convex_center {Coord : Type*}
    (center first second : Coord → ℝ)
    (hopposite : OppositeRays (first - center) (second - center)) :
    ∃ weight : ℝ, 0 < weight ∧ weight < 1 ∧
      center = weight • first + (1 - weight) • second := by
  obtain ⟨scalar, hscalar, hrelation⟩ := hopposite
  have hden : 0 < 1 - scalar := by linarith
  refine ⟨(-scalar) / (1 - scalar), div_pos (neg_pos.mpr hscalar) hden, ?_, ?_⟩
  · apply (div_lt_one hden).mpr
    linarith
  · funext k
    have hk := congrFun hrelation k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk
    change center k = ((-scalar) / (1 - scalar)) * first k +
      (1 - (-scalar) / (1 - scalar)) * second k
    field_simp [ne_of_gt hden]
    nlinarith

theorem convex_center_gives_opposite_differences {Coord : Type*}
    (center first second : Coord → ℝ) (weight : ℝ)
    (hweight : 0 < weight) (hweight1 : weight < 1)
    (hcenter : center = weight • first + (1 - weight) • second) :
    OppositeRays (first - center) (second - center) := by
  have hden : 0 < 1 - weight := by linarith
  refine ⟨(-weight) / (1 - weight), div_neg_of_neg_of_pos (neg_neg_of_pos hweight) hden, ?_⟩
  funext k
  have hk := congrFun hcenter k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk
  change second k - center k = ((-weight) / (1 - weight)) * (first k - center k)
  field_simp [ne_of_gt hden]
  nlinarith

/-- The complete finite row dichotomy for a public normalized coefficient
model. The outsider set records agent multiplicity. The third branch gives
an actual direction in the queried row's kernel, not an assumed oracle. -/
theorem public_coefficient_row_dichotomy {Agent Coord : Type*}
    [DecidableEq Agent] [Fintype Coord]
    (C : Agent → Coord → ℝ) (totals : Coord → ℝ) (queried : Agent)
    (outsiders : Finset Agent)
    (houtside : ∀ i, i ∈ outsiders ↔ C i ≠ C queried)
    (hnet : ∀ i, C i ⬝ᵥ totals = 1) :
    outsiders.card ≤ 1 ∨
    (∃ (first second : Agent) (weight : ℝ), first ≠ second ∧ outsiders = {first, second} ∧
      0 < weight ∧ weight < 1 ∧
      C queried = weight • C first + (1 - weight) • C second) ∨
    ∃ first second direction, first ≠ second ∧
      C queried ⬝ᵥ direction = 0 ∧
      0 < C first ⬝ᵥ direction ∧ 0 < C second ⬝ᵥ direction := by
  have hnonzero : ∀ i ∈ outsiders, C i - C queried ≠ 0 := by
    intro i hi hzero
    exact (houtside i).mp hi (sub_eq_zero.mp hzero)
  rcases finite_outsider_geometry outsiders (fun i => C i - C queried) hnonzero with
    hsmall | ⟨first, second, _, _, hdistinct, hset, hopposite⟩ |
      ⟨first, second, direction, _, _, hdistinct, hfirst, hsecond⟩
  · exact Or.inl hsmall
  · obtain ⟨weight, hweight, hweight1, hcenter⟩ :=
      opposite_differences_give_convex_center (C queried) (C first) (C second) hopposite
    exact Or.inr (Or.inl ⟨first, second, weight, hdistinct, hset, hweight, hweight1, hcenter⟩)
  · have hproject := projected_direction_separates (C queried) (C first) (C second)
      totals direction (hnet queried) (hnet first) (hnet second) hfirst hsecond
    exact Or.inr (Or.inr ⟨first, second, queryProjection (C queried) totals direction,
      hdistinct, hproject⟩)

#print axioms query_projection_annihilates
#print axioms coefficient_relation_preserved
#print axioms contrast_kernel_is_zero
#print axioms nonzero_perturbation_changes_comparison
#print axioms central_opposite_coefficients_complete_EF
#print axioms integer_pulse_meets_guards_and_exclusions
#print axioms correlated_pulse_preserves_obstruction
#print axioms separator_iff_not_opposite
#print axioms finite_outsider_geometry
#print axioms opposite_differences_give_convex_center
#print axioms public_coefficient_row_dichotomy

end EnvyFreeResearch.R4SignedLinear
