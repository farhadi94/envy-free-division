import Mathlib
import EnvyFreeResearch.R4Refinement
import EnvyFreeResearch.R4GlobalPotential

/-!
# Round 5 finite aggregate charging and rank-aware refinement

This module proves finite algebra, concrete moment-map dimension arguments,
and feasible support reduction. Continuous endpoint laws, conditional
expectation, physical interval realization and the complete protocols are not
axiomatized here.
-/

namespace EnvyFreeResearch.R5RankRefinement

open scoped BigOperators

section Aggregate

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

omit [Fintype Cell] in
/-- At most one endpoint group per recipient is represented by a finset.
Two marginal laws are dominated separately; no independence is assumed. -/
theorem aggregate_endpoint_density (reached : Finset Agent)
    (ν left right : Agent → Cell → ℝ) (q : ℝ) (hq : 0 < q)
    (hν : ∀ i c, 0 ≤ ν i c)
    (hleft : ∀ i ∈ reached, ∀ c, left i c ≤ (4 / q) * ν i c)
    (hright : ∀ i ∈ reached, ∀ c, right i c ≤ (4 / q) * ν i c)
    (c : Cell) :
    (∑ i ∈ reached, (left i c + right i c)) ≤ (8 / q) * ∑ i, ν i c := by
  calc
    (∑ i ∈ reached, (left i c + right i c)) ≤
        ∑ i ∈ reached, (8 / q) * ν i c := by
      apply Finset.sum_le_sum
      intro i hi
      have hl := hleft i hi c
      have hr := hright i hi c
      have heq : (8 / q) * ν i c = (4 / q) * ν i c + (4 / q) * ν i c := by ring
      rw [heq]
      exact add_le_add hl hr
    _ = (8 / q) * ∑ i ∈ reached, ν i c := by rw [Finset.mul_sum]
    _ ≤ (8 / q) * ∑ i, ν i c := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ reached)
        (fun i _ _ => hν i c)

/-- Adding recipient-specific dominating rows before charging the error avoids
an extra factor of the population size. -/
theorem aggregate_endpoint_charge (reached : Finset Agent)
    (ν left right : Agent → Cell → ℝ) (error μ : Cell → ℝ)
    (q : ℝ) (hq : 0 < q)
    (hν : ∀ i c, 0 ≤ ν i c) (he : ∀ c, 0 ≤ error c)
    (hmix : ∀ c, ∑ i, ν i c = (Fintype.card Agent : ℝ) * μ c)
    (hleft : ∀ i ∈ reached, ∀ c, left i c ≤ (4 / q) * ν i c)
    (hright : ∀ i ∈ reached, ∀ c, right i c ≤ (4 / q) * ν i c) :
    (∑ i ∈ reached, ∑ c, error c * (left i c + right i c)) ≤
      (8 * Fintype.card Agent / q) * ∑ c, error c * μ c := by
  rw [Finset.sum_comm]
  calc
    (∑ c, ∑ i ∈ reached, error c * (left i c + right i c)) ≤
        ∑ c, error c * ((8 / q) * ∑ i, ν i c) := by
      apply Finset.sum_le_sum
      intro c _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (aggregate_endpoint_density reached ν left right q hq hν hleft hright c) (he c)
    _ = (8 * Fintype.card Agent / q) * ∑ c, error c * μ c := by
      simp_rw [hmix]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- Finite nonnegative weighting preserves the aggregate charge estimate,
including outcome-dependent reached sets and endpoint laws. -/
theorem finite_expected_charge {Outcome : Type*} [Fintype Outcome]
    (weight charge baseline : Outcome → ℝ) (Λ : ℝ)
    (hw : ∀ ω, 0 ≤ weight ω) (hcharge : ∀ ω, charge ω ≤ Λ * baseline ω) :
    (∑ ω, weight ω * charge ω) ≤ Λ * ∑ ω, weight ω * baseline ω := by
  calc
    (∑ ω, weight ω * charge ω) ≤ ∑ ω, weight ω * (Λ * baseline ω) := by
      exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hcharge ω) (hw ω))
    _ = Λ * ∑ ω, weight ω * baseline ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

/-- A finite weighted Markov bound, derived from the actual bad-event indicator. -/
theorem finite_markov_bound {Outcome : Type*} [Fintype Outcome]
    (weight charge : Outcome → ℝ) (threshold : ℝ)
    (hw : ∀ ω, 0 ≤ weight ω) (hc : ∀ ω, 0 ≤ charge ω)
    (ht : 0 < threshold) :
    (∑ ω ∈ Finset.univ.filter (fun ω => threshold ≤ charge ω), weight ω) ≤
      (∑ ω, weight ω * charge ω) / threshold := by
  classical
  apply (le_div_iff₀ ht).mpr
  calc
    (∑ ω ∈ Finset.univ.filter (fun ω => threshold ≤ charge ω), weight ω) * threshold =
        ∑ ω ∈ Finset.univ.filter (fun ω => threshold ≤ charge ω), weight ω * threshold := by
      rw [Finset.sum_mul]
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => threshold ≤ charge ω), weight ω * charge ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 (hw ω)
    _ ≤ ∑ ω, weight ω * charge ω := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => mul_nonneg (hw ω) (hc ω))

end Aggregate

section Sensitivity

variable {Cell : Type*} [Fintype Cell]

theorem scalar_table_variation (c : ℝ) (σ : Cell → ℝ) :
    (∑ e, |c * σ e|) = |c| * ∑ e, |σ e| := by
  simp_rw [abs_mul]
  rw [Finset.mul_sum]

theorem scalar_normalized_cell (c : ℝ) (σ : Cell → ℝ) (e : Cell) (hc : c ≠ 0) :
    |c * σ e| / (∑ a, |c * σ a|) = |σ e| / (∑ a, |σ a|) := by
  rw [scalar_table_variation, abs_mul]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr hc)

theorem scalar_sensitivity_sum (σ : Cell → ℝ)
    (hσ : (∑ e, |σ e|) ≠ 0) :
    (∑ e, |σ e| / (∑ a, |σ a|)) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hσ

theorem zero_variation_coordinates (γ : Cell → ℝ) (hzero : (∑ e, |γ e|) = 0) :
    ∀ e, γ e = 0 := by
  intro e
  have hle : |γ e| ≤ ∑ a, |γ a| :=
    Finset.single_le_sum (fun a _ => abs_nonneg (γ a)) (Finset.mem_univ e)
  rw [hzero] at hle
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

theorem zero_variation_correction (γ z : Cell → ℝ) (hzero : (∑ e, |γ e|) = 0) :
    (∑ e, z e * γ e) = 0 := by
  simp_rw [zero_variation_coordinates γ hzero, mul_zero]
  simp

/-- A coordinatewise envelope controls every correction row simultaneously. -/
theorem weighted_coordinate_envelope (γ z h : Cell → ℝ) (D : ℝ)
    (hD : 0 < D) (hz : ∀ e, 0 ≤ z e)
    (henvelope : ∀ e, |γ e| / D ≤ h e) :
    |∑ e, z e * γ e| / D ≤ ∑ e, z e * h e := by
  apply (div_le_iff₀ hD).mpr
  calc
    |∑ e, z e * γ e| ≤ ∑ e, |z e * γ e| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e, z e * |γ e| := by simp_rw [abs_mul, abs_of_nonneg (hz _)]
    _ ≤ ∑ e, z e * (h e * D) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hD).mp (henvelope e)) (hz e)
    _ = (∑ e, z e * h e) * D := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- Bounding each coordinate's mean inclusion by p charges the envelope once. -/
theorem finite_expected_envelope {Outcome : Type*} [Fintype Outcome]
    (weight : Outcome → ℝ) (z : Outcome → Cell → ℝ) (h : Cell → ℝ) (p d : ℝ)
    (hh : ∀ e, 0 ≤ h e) (hp : 0 ≤ p)
    (hinclusion : ∀ e, (∑ ω, weight ω * z ω e) ≤ p)
    (hsensitivity : ∑ e, h e ≤ d) :
    (∑ ω, weight ω * ∑ e, z ω e * h e) ≤ p * d := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ ω, weight ω * (z ω e * h e)) =
        ∑ e, (∑ ω, weight ω * z ω e) * h e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ e, p * h e := Finset.sum_le_sum
      (fun e _ => mul_le_mul_of_nonneg_right (hinclusion e) (hh e))
    _ = p * ∑ e, h e := by rw [Finset.mul_sum]
    _ ≤ p * d := mul_le_mul_of_nonneg_left hsensitivity hp

theorem convex_mesh_bound (t left right η : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hl : 0 ≤ left ∧ left ≤ η) (hr : 0 ≤ right ∧ right ≤ η) :
    0 ≤ (1 - t) * left + t * right ∧ (1 - t) * left + t * right ≤ η := by
  constructor
  · exact add_nonneg (mul_nonneg (by linarith [ht.2]) hl.1) (mul_nonneg ht.1 hr.1)
  · have hL := mul_le_mul_of_nonneg_left hl.2 (show 0 ≤ 1 - t by linarith [ht.2])
    have hR := mul_le_mul_of_nonneg_left hr.2 ht.1
    nlinarith

theorem normalized_affine_mesh_bound (t leftTotal rightTotal leftValue rightValue η : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (hL : 0 < leftTotal) (hR : 0 < rightTotal)
    (hl : 0 ≤ leftValue / leftTotal ∧ leftValue / leftTotal ≤ η)
    (hr : 0 ≤ rightValue / rightTotal ∧ rightValue / rightTotal ≤ η) :
    ((1 - t) * leftValue + t * rightValue) /
      ((1 - t) * leftTotal + t * rightTotal) ≤ η := by
  rw [R4Refinement.convex_normalization_identity t leftTotal rightTotal leftValue rightValue ht hL hR]
  exact (convex_mesh_bound _ _ _ η
    (R4Refinement.normalized_coefficient_in_unit t leftTotal rightTotal ht hL hR) hl hr).2

end Sensitivity

section Rank

variable {Variable Equation : Type*} [Fintype Variable] [Fintype Equation]

/-- A dimension argument over the actual finite linear map, not an assumed
support-cardinality conclusion. -/
theorem real_kernel_exists (L : (Variable → ℝ) →ₗ[ℝ] (Equation → ℝ))
    (hshort : Fintype.card Equation < Fintype.card Variable) :
    ∃ z, z ≠ 0 ∧ L z = 0 := by
  classical
  by_contra hnone
  have hzero : ∀ z, L z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    exact hnone ⟨z, hne, hz⟩
  have hinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_pi] at hd
  omega

variable {Cell Feature Recipient : Type*}
  [Fintype Cell] [DecidableEq Cell] [Fintype Feature] [Fintype Recipient]

noncomputable def refinementMomentMap (cell : Variable → Cell)
    (coefficient : Feature → Recipient → Variable → ℝ) :
    (Variable → ℝ) →ₗ[ℝ] ((Cell ⊕ (Feature × Recipient)) → ℝ) := by
  exact Matrix.mulVecLin (fun row v => match row with
    | Sum.inl c => if cell v = c then 1 else 0
    | Sum.inr pair => coefficient pair.1 pair.2 v)

omit [Fintype Cell] [Fintype Feature] [Fintype Recipient] in
theorem refinementMomentMap_cell (cell : Variable → Cell)
    (coefficient : Feature → Recipient → Variable → ℝ) (z : Variable → ℝ) (c : Cell) :
    refinementMomentMap cell coefficient z (Sum.inl c) =
      ∑ v, if cell v = c then z v else 0 := by
  classical
  change (∑ v, (if cell v = c then (1 : ℝ) else 0) * z v) = _
  simp only [ite_mul, one_mul, zero_mul]

omit [Fintype Cell] [Fintype Feature] [Fintype Recipient] in
theorem refinementMomentMap_moment (cell : Variable → Cell)
    (coefficient : Feature → Recipient → Variable → ℝ) (z : Variable → ℝ)
    (a : Feature) (j : Recipient) :
    refinementMomentMap cell coefficient z (Sum.inr (a, j)) =
      ∑ v, coefficient a j v * z v := by
  rfl

/-- More split cells than r*k produce a genuine nonzero direction preserving
all cell sums and all r basis moments for each of k recipients. -/
theorem split_cell_kernel_exists (cell : Variable → Cell)
    (coefficient : Feature → Recipient → Variable → ℝ)
    (htwo : 2 * Fintype.card Cell ≤ Fintype.card Variable)
    (hover : Fintype.card Feature * Fintype.card Recipient < Fintype.card Cell) :
    ∃ z : Variable → ℝ, z ≠ 0 ∧
      (∀ c, (∑ v, if cell v = c then z v else 0) = 0) ∧
      (∀ a j, (∑ v, coefficient a j v * z v) = 0) := by
  have hshort : Fintype.card (Cell ⊕ (Feature × Recipient)) < Fintype.card Variable := by
    simp only [Fintype.card_sum, Fintype.card_prod]
    omega
  obtain ⟨z, hz, hLz⟩ := real_kernel_exists (refinementMomentMap cell coefficient) hshort
  refine ⟨z, hz, ?_, ?_⟩
  · intro c
    have h := congrFun hLz (Sum.inl c)
    simpa only [refinementMomentMap_cell, Pi.zero_apply] using h
  · intro a j
    have h := congrFun hLz (Sum.inr (a, j))
    simpa only [refinementMomentMap_moment, Pi.zero_apply] using h

/-- Actual support fibers, each of size at least two, supply the needed variable
count. Duplicate recipient indices in different cells are different variables. -/
theorem split_cell_kernel_from_fibers (Support : Cell → Type*)
    [∀ c, Fintype (Support c)]
    (coefficient : Feature → Recipient → (Σ c, Support c) → ℝ)
    (htwo : ∀ c, 2 ≤ Fintype.card (Support c))
    (hover : Fintype.card Feature * Fintype.card Recipient < Fintype.card Cell) :
    ∃ z : (Σ c, Support c) → ℝ, z ≠ 0 ∧
      (∀ c, (∑ v, if v.1 = c then z v else 0) = 0) ∧
      (∀ a j, (∑ v, coefficient a j v * z v) = 0) := by
  apply split_cell_kernel_exists Sigma.fst coefficient _ hover
  rw [Fintype.card_sigma]
  calc
    2 * Fintype.card Cell = ∑ _c : Cell, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ c, Fintype.card (Support c) := Finset.sum_le_sum (fun c _ => htwo c)

/-- The at-least-two support condition follows from an actual normalized
fractional color vector, using the earlier finite certificate. -/
theorem actual_fractional_fiber_has_two {Color : Type*} [Fintype Color]
    (x : Color → ℝ) (hx : ∀ j, 0 ≤ x j) (hsum : ∑ j, x j = 1)
    (hsplit : ∃ j, 0 < x j ∧ x j < 1) :
    2 ≤ Fintype.card {j : Color // 0 < x j ∧ x j < 1} := by
  classical
  obtain ⟨j, hj⟩ := hsplit
  simpa only [Fintype.card_subtype] using
    R3Refinement.fractional_row_has_two_variables x hx hsum j hj

theorem basis_moments_preserve_observer (basis : Feature → Variable → ℝ)
    (coeff : Feature → ℝ) (z : Variable → ℝ)
    (hzero : ∀ a, (∑ v, basis a v * z v) = 0) :
    (∑ v, (∑ a, coeff a * basis a v) * z v) = 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  calc
    (∑ v, coeff a * basis a v * z v) = coeff a * ∑ v, basis a v * z v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = 0 := by rw [hzero, mul_zero]

end Rank

section SupportReduction

variable {Variable Equation : Type*} [Fintype Variable] [Fintype Equation]

/-- A nonzero zero-sum direction has a positive coordinate. -/
theorem zero_sum_direction_has_positive (z : Variable → ℝ)
    (hz : z ≠ 0) (hsum : ∑ v, z v = 0) : ∃ v, 0 < z v := by
  classical
  have hne : ∃ v ∈ (Finset.univ : Finset Variable), z v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hz
    funext v
    exact hn v (Finset.mem_univ v)
  obtain ⟨v, _, hv⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero z hsum hne
  exact ⟨v, hv⟩

/-- The first positive ratio makes an actual feasible step and kills at least
one positive variable. This is the finite floating-variable operation. -/
theorem positive_support_step (x z : Variable → ℝ)
    (hx : ∀ v, 0 < x v) (hz : ∃ v, 0 < z v) :
    ∃ t : ℝ, 0 < t ∧ (∀ v, 0 ≤ x v - t * z v) ∧
      (∃ v, x v - t * z v = 0) := by
  classical
  let positive := Finset.univ.filter (fun v => 0 < z v)
  have hnonempty : positive.Nonempty := by
    obtain ⟨v, hv⟩ := hz
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
  obtain ⟨v, hv, hmin⟩ := positive.exists_min_image (fun a => x a / z a) hnonempty
  have hvpos : 0 < z v := (Finset.mem_filter.mp hv).2
  refine ⟨x v / z v, div_pos (hx v) hvpos, ?_, v, ?_⟩
  · intro a
    by_cases ha : 0 < z a
    · have hratio := hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
      have hmul := (le_div_iff₀ ha).mp hratio
      linarith
    · have hprod : x v / z v * z a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hx v).le hvpos.le) (le_of_not_gt ha)
      linarith [hx a]
  · rw [div_mul_cancel₀ _ hvpos.ne', sub_self]

omit [Fintype Variable] [Fintype Equation] in
theorem kernel_step_preserves_constraints
    (L : (Variable → ℝ) →ₗ[ℝ] (Equation → ℝ)) (x z : Variable → ℝ)
    (t : ℝ) (hz : L z = 0) : L (x - t • z) = L x := by
  rw [map_sub, map_smul, hz, smul_zero, sub_zero]

omit [Fintype Equation] in
/-- A zero-sum kernel direction gives a smaller positive support with exactly
the same linear constraints. No optimum or sparse solution is assumed. -/
theorem kernel_reduces_positive_support
    (L : (Variable → ℝ) →ₗ[ℝ] (Equation → ℝ)) (x z : Variable → ℝ)
    (hx : ∀ v, 0 < x v) (hz : z ≠ 0) (hzero : L z = 0)
    (hsum : ∑ v, z v = 0) :
    ∃ y : Variable → ℝ, (∀ v, 0 ≤ y v) ∧ L y = L x ∧
      (Finset.univ.filter (fun v => 0 < y v)).card < Fintype.card Variable := by
  classical
  obtain ⟨t, _, hnonneg, v, hv⟩ :=
    positive_support_step x z hx (zero_sum_direction_has_positive z hz hsum)
  refine ⟨x - t • z, hnonneg, kernel_step_preserves_constraints L x z t hzero, ?_⟩
  have hproper : (Finset.univ.filter (fun a => 0 < (x - t • z) a)) ⊂ Finset.univ := by
    apply Finset.filter_ssubset.mpr
    refine ⟨v, Finset.mem_univ v, ?_⟩
    change ¬ 0 < x v - t * z v
    rw [hv]
    exact lt_irrefl 0
  simpa using Finset.card_lt_card hproper

/-- The current split-cell constraints force a global zero sum, providing the
sign condition needed by the support-reduction operation. -/
theorem cell_zero_sums_give_total_zero {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (cell : Variable → Cell) (z : Variable → ℝ)
    (hz : ∀ c, (∑ v, if cell v = c then z v else 0) = 0) :
    (∑ v, z v) = 0 := by
  have hsum : (∑ c, ∑ v, if cell v = c then z v else 0) = 0 := by
    simp_rw [hz]
    simp
  rw [Finset.sum_comm] at hsum
  simpa using hsum

/-- Combine the actual rank-deficient moment map with the feasible support
step. This is the rank-aware floating operation used before whole-cell rounding. -/
theorem excessive_split_cells_admit_support_reduction
    {Cell Feature Recipient : Type*} [Fintype Cell] [DecidableEq Cell]
    [Fintype Feature] [Fintype Recipient]
    (cell : Variable → Cell) (coefficient : Feature → Recipient → Variable → ℝ)
    (x : Variable → ℝ) (hx : ∀ v, 0 < x v)
    (htwo : 2 * Fintype.card Cell ≤ Fintype.card Variable)
    (hover : Fintype.card Feature * Fintype.card Recipient < Fintype.card Cell) :
    ∃ y : Variable → ℝ, (∀ v, 0 ≤ y v) ∧
      refinementMomentMap cell coefficient y = refinementMomentMap cell coefficient x ∧
      (Finset.univ.filter (fun v => 0 < y v)).card < Fintype.card Variable := by
  classical
  obtain ⟨z, hz, hcell, hmoment⟩ := split_cell_kernel_exists cell coefficient htwo hover
  have hzero : refinementMomentMap cell coefficient z = 0 := by
    funext row
    cases row with
    | inl c => simpa only [refinementMomentMap_cell, Pi.zero_apply] using hcell c
    | inr pair =>
      change (∑ v, coefficient pair.1 pair.2 v * z v) = 0
      exact hmoment pair.1 pair.2
  exact kernel_reduces_positive_support _ x z hx hz hzero
    (cell_zero_sums_give_total_zero cell z hcell)

/-- On a nonnegative cell of total one, every surviving coordinate is at most one. -/
theorem cell_coordinate_le_one {Cell : Type*} [DecidableEq Cell]
    (cell : Variable → Cell) (x : Variable → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hcell : ∀ c, (∑ v, if cell v = c then x v else 0) = 1)
    (v : Variable) : x v ≤ 1 := by
  classical
  have hsingle : (if cell v = cell v then x v else 0) ≤
      ∑ a, if cell a = cell v then x a else 0 := by
    apply Finset.single_le_sum (s := Finset.univ) (a := v)
      (f := fun a => if cell a = cell v then x a else 0)
    · intro a _
      split_ifs
      · exact hx a
      · exact le_rfl
    · exact Finset.mem_univ v
  simpa [hcell] using hsingle

end SupportReduction

/-- Actual strict support decreases give a bounded number of floating steps.
This reuses the anchored finite progress lemma with eliminated variables as
potential; it does not assume an execution's length bound. -/
theorem support_elimination_count (count : ℕ → ℕ) (steps : ℕ)
    (hstep : ∀ t < steps, count (t + 1) + 1 ≤ count t) : steps ≤ count 0 := by
  have hbound : ∀ t, t ≤ steps → count t ≤ count 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hnext := hstep t (by omega)
      omega
  have hprogress : ∀ t < steps, (count 0 - count t) + 1 ≤ count 0 - count (t + 1) := by
    intro t ht
    have hcur := hbound t (by omega)
    have hnext := hstep t ht
    omega
  have h := R4GlobalPotential.interleaved_progress_bound
    (fun t => count 0 - count t) (fun _ => 1) steps (count 0)
    hprogress (Nat.sub_le _ _)
  simpa using h

theorem no_infinite_support_elimination (count : ℕ → ℕ) :
    ¬ (∀ t, count (t + 1) < count t) := by
  intro h
  have hbound := support_elimination_count count (count 0 + 1)
    (fun t _ => by have ht := h t; omega)
  omega

section WholeCell

variable {Cell : Type*} [Fintype Cell] [DecidableEq Cell]

/-- Rank-aware whole-cell error, with the error on a changed variable derived
from its actual before/after coefficients. -/
theorem fractional_rounding_observer_error (live : Finset Cell)
    (γ before after : Cell → ℝ) (A : ℝ) (r k : ℕ)
    (hA : 0 ≤ A) (hcount : live.card ≤ r * k)
    (hγ : ∀ c ∈ live, |γ c| ≤ A)
    (hbefore : ∀ c ∈ live, 0 ≤ before c ∧ before c ≤ 1)
    (hafter : ∀ c ∈ live, 0 ≤ after c ∧ after c ≤ 1)
    (hfrozen : ∀ c ∉ live, after c = before c)
    (hbalanced : ∑ c, γ c * before c = 0) :
    |∑ c, γ c * after c| ≤ ((r * k : ℕ) : ℝ) * A := by
  have h := NearExact.finite_error_bound_of_card_le live
    (fun c => γ c * after c) (fun c => γ c * before c) A (r * k) hA hcount
  rw [hbalanced, sub_zero] at h
  apply h
  · intro c hc
    have hdiff : |after c - before c| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [(hbefore c hc).1, (hbefore c hc).2,
        (hafter c hc).1, (hafter c hc).2]
    rw [← mul_sub, abs_mul]
    calc
      |γ c| * |after c - before c| ≤ |γ c| * 1 :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
      _ ≤ A := by simpa using hγ c hc
  · intro c hc
    rw [hfrozen c hc]

end WholeCell

section ScalarSeeds

/-- A threshold inserts positive witnesses and removes negative witnesses.
The cells are already distinct and indexed in selection order. -/
noncomputable def seedScore (σ : ℕ → ℝ) (L t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L, if j < t then max (σ j) 0 else min (σ j) 0

theorem seed_score_increment (σ : ℕ → ℝ) (L t : ℕ) (ht : t < L) :
    seedScore σ L (t + 1) - seedScore σ L t = |σ t| := by
  unfold seedScore
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j ∈ Finset.range L,
      ((if j < t + 1 then max (σ j) 0 else min (σ j) 0) -
       (if j < t then max (σ j) 0 else min (σ j) 0))) =
        max (σ t) 0 - min (σ t) 0 := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro j _ hne
        have hiff : j < t + 1 ↔ j < t := by omega
        simp only [hiff, sub_self]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr ht))
    _ = |σ t| := by
      by_cases h : 0 ≤ σ t
      · rw [max_eq_left h, min_eq_right h, sub_zero, abs_of_nonneg h]
      · have h' : σ t ≤ 0 := le_of_not_ge h
        rw [max_eq_right h', min_eq_left h', zero_sub, abs_of_nonpos h']

/-- The selected witness bound gives actual threshold spacing for the signed
seed construction, including both insertion and removal cases. -/
theorem seed_score_spacing (σ : ℕ → ℝ) (L : ℕ) (gap : ℝ)
    (hwitness : ∀ t < L, gap ≤ |σ t|) :
    ∀ a b, a ≤ b → b ≤ L →
      ((b - a : ℕ) : ℝ) * gap ≤ seedScore σ L b - seedScore σ L a := by
  intro a b
  induction b generalizing a with
  | zero =>
    intro hab _
    have ha : a = 0 := by omega
    simp [ha]
  | succ b ih =>
    intro hab hb
    by_cases heq : a = b + 1
    · simp [heq]
    · have hab' : a ≤ b := by omega
      have hprev := ih a hab' (by omega)
      have hinc := seed_score_increment σ L b (by omega)
      have hw := hwitness b (by omega)
      have hcast : ((b + 1 - a : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) + 1 := by
        have hnat : b + 1 - a = (b - a) + 1 := by omega
        rw [hnat, Nat.cast_add, Nat.cast_one]
      rw [hcast]
      nlinarith

theorem bad_threshold_width (σ : ℕ → ℝ) (L a b : ℕ) (gap center radius : ℝ)
    (hwitness : ∀ t < L, gap ≤ |σ t|) (hab : a ≤ b) (hb : b ≤ L)
    (haBad : |seedScore σ L a - center| < radius)
    (hbBad : |seedScore σ L b - center| < radius) :
    ((b - a : ℕ) : ℝ) * gap < 2 * radius := by
  have hspace := seed_score_spacing σ L gap hwitness a b hab hb
  have ha := (abs_lt.mp haBad).1
  have hb' := (abs_lt.mp hbBad).2
  linarith

end ScalarSeeds

section Parameters

noncomputable def repairLambda (s : ℝ) : ℝ := s / 8
noncomputable def repairSample (s : ℝ) : ℝ := 512 * s ^ 9
noncomputable def repairReserve (s : ℝ) : ℝ := 1 / s ^ 4
noncomputable def repairMesh (s : ℝ) : ℝ := 1 / (32 * s ^ 9)
noncomputable def repairCellSize (s : ℝ) : ℝ := 1 / (16 * s ^ 5)
noncomputable def repairAccuracy (s : ℝ) : ℝ := 1 / (16777216 * s ^ 4)

theorem sample_mesh_identity (s : ℝ) (hs : s ≠ 0) :
    repairMesh s * repairSample s = 16 := by
  unfold repairMesh repairSample
  field_simp
  ring

theorem reserve_accuracy_sample_identity (s : ℝ) (hs : s ≠ 0) :
    repairReserve s * repairAccuracy s * repairSample s = s / 32768 := by
  unfold repairReserve repairAccuracy repairSample
  field_simp
  ring

theorem correction_accuracy_identity (s : ℝ) (hs : s ≠ 0) :
    repairCellSize s / repairAccuracy s = 1048576 / s := by
  unfold repairCellSize repairAccuracy
  field_simp
  ring

theorem reserve_table_identity (s : ℝ) (hs : s ≠ 0) :
    1024 * repairReserve s * repairSample s = 524288 * s ^ 5 := by
  unfold repairReserve repairSample
  field_simp
  ring

theorem payment_accuracy_identity (s : ℝ) (hs : s ≠ 0) :
    repairAccuracy s = repairLambda s / (4 * (1024 * repairReserve s * repairSample s)) := by
  rw [reserve_table_identity s hs]
  unfold repairAccuracy repairLambda
  field_simp
  ring

theorem seed_affordability_identity (s : ℝ) (hs : s ≠ 0) :
    s ^ 3 * repairCellSize s = 1 / (16 * s ^ 2) := by
  unfold repairCellSize
  field_simp

theorem supply_error_identity (s k : ℝ) (hs : s ≠ 0) :
    k * repairLambda s * repairCellSize s = k / (128 * s ^ 4) := by
  unfold repairLambda repairCellSize
  field_simp
  ring

theorem coarse_mesh_fits (s : ℝ) (hs : s ≠ 0) :
    6 / (repairMesh s * repairSample s) = 3 / 8 := by
  rw [sample_mesh_identity s hs]
  norm_num

theorem repair_accuracy_le_one (s : ℝ) (hs : 1 ≤ s) : repairAccuracy s ≤ 1 := by
  have hpow : 1 ≤ s ^ 4 := one_le_pow₀ hs
  unfold repairAccuracy
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16777216 * s ^ 4)).mpr
  nlinarith

/-- Exact arithmetic of the improved aggregate endpoint term. -/
theorem rank_two_interpolation_budget (s k : ℝ) (hs : 1 ≤ s) (hk : 0 ≤ k) :
    16 * k * (1 + repairAccuracy s) /
      (repairReserve s * repairAccuracy s * (repairSample s + 1)) ≤
      1048576 * (k / s) := by
  have hspos : 0 < s := by linarith
  have hq : 0 < repairReserve s := by unfold repairReserve; positivity
  have hb : 0 < repairAccuracy s := by unfold repairAccuracy; positivity
  have hm : 0 < repairSample s := by unfold repairSample; positivity
  have hb1 := repair_accuracy_le_one s hs
  have hden : 0 < repairReserve s * repairAccuracy s * (repairSample s + 1) := by positivity
  have hbase : 0 < repairReserve s * repairAccuracy s * repairSample s := by positivity
  have hcompare : repairReserve s * repairAccuracy s * repairSample s ≤
      repairReserve s * repairAccuracy s * (repairSample s + 1) := by nlinarith
  calc
    16 * k * (1 + repairAccuracy s) /
        (repairReserve s * repairAccuracy s * (repairSample s + 1)) ≤
        32 * k / (repairReserve s * repairAccuracy s * (repairSample s + 1)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith
    _ ≤ 32 * k / (repairReserve s * repairAccuracy s * repairSample s) :=
      div_le_div_of_nonneg_left (by positivity) hbase hcompare
    _ = 1048576 * (k / s) := by
      rw [reserve_accuracy_sample_identity s hspos.ne']
      field_simp
      ring

theorem rank_two_correction_budget (s k : ℝ) (hs : s ≠ 0) :
    2 * k * repairCellSize s / repairAccuracy s = 2097152 * (k / s) := by
  rw [mul_div_assoc, correction_accuracy_identity s hs]
  ring

theorem grouped_payment_failure_small (s k : ℝ) (hs : 1 ≤ s) (hk : 0 ≤ k)
    (hκ : k / s ≤ 1 / 1099511627776) :
    16 * k * (1 + repairAccuracy s) /
        (repairReserve s * repairAccuracy s * (repairSample s + 1)) +
      2 * k * repairCellSize s / repairAccuracy s < 1 / 512 := by
  have hi := rank_two_interpolation_budget s k hs hk
  have hc := rank_two_correction_budget s k (by linarith : s ≠ 0)
  rw [hc]
  linarith

theorem rank_two_whole_cell_accuracy (s k A : ℝ)
    (hcount : 32 * k ≤ s) (hA : 0 ≤ A) :
    2 * k * A ≤ repairLambda s * A / 2 := by
  unfold repairLambda
  have h := mul_le_mul_of_nonneg_right hcount hA
  nlinarith

/-- The inherited payment and all-row mesh inequalities obstruct the rejected
general retuning. This bounds a proof budget, not an actual failure probability. -/
theorem general_correction_budget_barrier (k q m b η lam : ℝ)
    (hq : 0 < q) (hb : 0 < b) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hpayment : 4096 * q * m * b ≤ lam) (hmesh : 2 * k ≤ η * m) :
    32768 * k ^ 3 / lam ≤ 4 * k ^ 2 * η / (q * b) := by
  apply (div_le_div_iff₀ hlam (mul_pos hq hb)).mpr
  have h1 := mul_le_mul_of_nonneg_left hpayment (show 0 ≤ 4 * k ^ 2 * η by positivity)
  have h2 := mul_le_mul_of_nonneg_left hmesh (show 0 ≤ 16384 * k ^ 2 * q * b by positivity)
  nlinarith

end Parameters

end EnvyFreeResearch.R5RankRefinement
