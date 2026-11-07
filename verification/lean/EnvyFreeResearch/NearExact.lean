import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Finite certificates for rounding a fractional near-exact allocation

No linear-programming existence or interval geometry is axiomatized here.
The inputs record actual cell values and the inequalities justified by a
nonnegative additive observer measure. In particular, the observer need not
assign values in proportion to interval length within a cell.
-/

namespace EnvyFreeResearch.NearExact

open scoped BigOperators

/-- A finite set of bounded per-cell errors bounds the whole-bundle error. -/
theorem finite_error_bound {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (changed : Finset Cell) (actual target : Cell → ℝ) (δ : ℝ)
    (hsmall : ∀ c ∈ changed, |actual c - target c| ≤ δ)
    (hagrees : ∀ c ∉ changed, actual c = target c) :
    |(∑ c, actual c) - (∑ c, target c)| ≤ (changed.card : ℝ) * δ := by
  have hsupport : ∑ c ∈ changed, (actual c - target c) =
      ∑ c, (actual c - target c) := by
    apply Finset.sum_subset (Finset.subset_univ changed)
    intro c _ hc
    simp [hagrees c hc]
  rw [← Finset.sum_sub_distrib, ← hsupport]
  calc
    |∑ c ∈ changed, (actual c - target c)| ≤
        ∑ c ∈ changed, |actual c - target c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ changed, δ := Finset.sum_le_sum hsmall
    _ = (changed.card : ℝ) * δ := by simp

/-- Error at most Bδ when at most B cells changed. -/
theorem finite_error_bound_of_card_le {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (changed : Finset Cell) (actual target : Cell → ℝ) (δ : ℝ) (B : ℕ)
    (hδ : 0 ≤ δ) (hcard : changed.card ≤ B)
    (hsmall : ∀ c ∈ changed, |actual c - target c| ≤ δ)
    (hagrees : ∀ c ∉ changed, actual c = target c) :
    |(∑ c, actual c) - (∑ c, target c)| ≤ (B : ℝ) * δ := by
  apply le_trans (finite_error_bound changed actual target δ hsmall hagrees)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hδ

/-- On one nonnegative cell, any actual subset and any fractional target differ
by at most the whole-cell value. This does not require a constant density. -/
theorem one_cell_rounding_error (cost actual fraction δ : ℝ)
    (hcost : 0 ≤ cost) (hcostδ : cost ≤ δ)
    (hactual0 : 0 ≤ actual) (hactual1 : actual ≤ cost)
    (hf0 : 0 ≤ fraction) (hf1 : fraction ≤ 1) :
    |actual - fraction * cost| ≤ δ := by
  have htarget0 : 0 ≤ fraction * cost := mul_nonneg hf0 hcost
  have htarget1 : fraction * cost ≤ cost := by nlinarith
  apply abs_le.mpr
  constructor <;> linarith

/-- A bundle rounding certificate with at most B small fractional cells. -/
theorem rounded_bundle_error {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (changed : Finset Cell) (cost actual fraction : Cell → ℝ) (δ : ℝ) (B : ℕ)
    (hδ : 0 ≤ δ) (hcard : changed.card ≤ B)
    (hcost : ∀ c ∈ changed, 0 ≤ cost c ∧ cost c ≤ δ)
    (hactual : ∀ c ∈ changed, 0 ≤ actual c ∧ actual c ≤ cost c)
    (hfraction : ∀ c ∈ changed, 0 ≤ fraction c ∧ fraction c ≤ 1)
    (hagrees : ∀ c ∉ changed, actual c = fraction c * cost c) :
    |(∑ c, actual c) - (∑ c, fraction c * cost c)| ≤ (B : ℝ) * δ := by
  apply finite_error_bound_of_card_le changed actual (fun c => fraction c * cost c)
    δ B hδ hcard _ hagrees
  intro c hc
  exact one_cell_rounding_error (cost c) (actual c) (fraction c) δ
    (hcost c hc).1 (hcost c hc).2 (hactual c hc).1 (hactual c hc).2
    (hfraction c hc).1 (hfraction c hc).2

/-- If every cell gives the designated cutter its prescribed fraction exactly,
then its total target is also exact. Geometry must establish the hypotheses. -/
theorem designated_cutter_exact {Cell : Type*} [Fintype Cell]
    (cost actual fraction : Cell → ℝ)
    (hexact : ∀ c, actual c = fraction c * cost c) :
    (∑ c, actual c) = ∑ c, fraction c * cost c := by
  exact Finset.sum_congr rfl (fun c _ => hexact c)

/-- A common fractional target simplifies to that fraction of the total cost. -/
theorem designated_cutter_common_fraction {Cell : Type*} [Fintype Cell]
    (cost actual : Cell → ℝ) (fraction : ℝ)
    (hexact : ∀ c, actual c = fraction * cost c) :
    (∑ c, actual c) = fraction * ∑ c, cost c := by
  calc
    (∑ c, actual c) = ∑ c, fraction * cost c :=
      Finset.sum_congr rfl (fun c _ => hexact c)
    _ = fraction * ∑ c, cost c := by rw [Finset.mul_sum]

/-- Per-bundle target errors give a two-sided envy error of at most 2ε. -/
theorem envy_error_from_common_target (own other target ε : ℝ)
    (hown : |own - target| ≤ ε) (hother : |other - target| ≤ ε) :
    other - own ≤ 2 * ε := by
  have ho := abs_le.mp hown
  have ht := abs_le.mp hother
  linarith

#print axioms finite_error_bound
#print axioms rounded_bundle_error
#print axioms designated_cutter_exact
#print axioms designated_cutter_common_fraction
#print axioms envy_error_from_common_target

end EnvyFreeResearch.NearExact
