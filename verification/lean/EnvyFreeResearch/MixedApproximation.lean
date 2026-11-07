import EnvyFreeResearch.R6MixedMonteCarlo

/-!
Finite supporting inequalities for the combined additive/multiplicative
mixed-resource lower bound. This file does not formalize the continuous query-protection,
measure-theoretic sampling, or fixed-input probability argument.
-/

namespace EnvyFreeResearch.MixedApproximation

open scoped BigOperators
open R6MixedMonteCarlo

variable {Agent : Type*} [DecidableEq Agent]

def RelaxedEF (value : Agent → Agent → ℝ) (a ε : ℝ) : Prop :=
  ∀ i j, a * value i j - value i i ≤ ε

theorem exact_comparison_implies_mult {a own other : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hown : 0 ≤ own)
    (hef : other ≤ own) : a * other ≤ own := by
  calc
    a * other ≤ a * own := mul_le_mul_of_nonneg_left hef ha
    _ ≤ 1 * own := mul_le_mul_of_nonneg_right ha1 hown
    _ = own := one_mul own

theorem coarse_forcing {a H left own other : ℝ}
    (ha : 0 ≤ a) (hown : own ≤ H) (hother : left - H ≤ other)
    (hforce : (1 + a) * H + a ≤ a * left) :
    a ≤ a * other - own := by
  have := mul_le_mul_of_nonneg_left hother ha
  nlinarith

theorem comparison_discrepancy {a gap own other coarseOwn coarseOther D : ℝ}
    (ha : 0 ≤ a)
    (hown : |coarseOwn - own| ≤ D)
    (hother : |coarseOther - other| ≤ D)
    (hcoarse : gap ≤ a * coarseOther - coarseOwn)
    (hfair : a * other - own ≤ 0) :
    gap ≤ (1 + a) * D := by
  have hownLower := (abs_le.mp hown).1
  have hotherUpper := (abs_le.mp hother).2
  have := mul_le_mul_of_nonneg_left hotherUpper ha
  nlinarith

theorem weighted_pulse_lower (a mass : ℝ) (positive negative own other : Agent)
    (ha : 0 ≤ a) (hmass : 0 ≤ mass) :
    -(1 + a) * mass ≤
      a * pulse mass positive negative other - pulse mass positive negative own := by
  have ho := (pulse_value_bounds mass positive negative own hmass).2
  have ht := (pulse_value_bounds mass positive negative other hmass).1
  have := mul_le_mul_of_nonneg_left ht ha
  nlinarith

theorem separated_weighted_gain (a mass : ℝ) (positive negative observer : Agent)
    (hmass : 0 ≤ mass) (hseparated : positive ≠ negative)
    (hobserver : observer ≠ positive) :
    a * mass ≤ a * pulse mass positive negative positive -
      pulse mass positive negative observer := by
  by_cases hn : negative = observer
  · subst observer
    simp [pulse, hseparated, hseparated.symm]
    linarith
  · simp [pulse, hseparated.symm, hobserver.symm, hn]

theorem weighted_sum_at_last (a : ℝ) (mass : ℕ → ℝ)
    (positive negative : ℕ → Agent) (L r : ℕ) (own other : Agent)
    (hr : r < L) (hlater : ∀ s < L, r < s → positive s = negative s) :
    (∑ s ∈ Finset.range L,
      (a * pulse (mass s) (positive s) (negative s) other -
        pulse (mass s) (positive s) (negative s) own)) =
      (∑ s ∈ Finset.range r,
        (a * pulse (mass s) (positive s) (negative s) other -
          pulse (mass s) (positive s) (negative s) own)) +
        (a * pulse (mass r) (positive r) (negative r) other -
          pulse (mass r) (positive r) (negative r) own) := by
  rw [← Finset.sum_range_succ]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hr))
  intro s hs hnot
  have hsL := Finset.mem_range.mp hs
  have hrs : r < s := by simp only [Finset.mem_range] at hnot; omega
  rw [hlater s hsL hrs, coassigned_pulse_zero, coassigned_pulse_zero]
  ring

theorem last_separated_forces_failure (a ε : ℝ)
    (base : Agent → Agent → ℝ) (mass : ℕ → ℝ)
    (positive negative : ℕ → Agent) (L r : ℕ) (T : ℝ) (observer : Agent)
    (ha : 0 ≤ a) (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ s < L, 0 ≤ mass s)
    (hr : r < L) (hseparated : positive r ≠ negative r)
    (hlater : ∀ s < L, r < s → positive s = negative s)
    (hobserver : observer ≠ positive r)
    (hlarge : (1 + a) * (T + ∑ s ∈ Finset.range r, mass s) + ε < a * mass r) :
    ε < a * perturbed base mass positive negative L observer (positive r) -
      perturbed base mass positive negative L observer observer := by
  have hbaseLower : -(1 + a) * T ≤
      a * base observer (positive r) - base observer observer := by
    have ho := (abs_le.mp (hbase observer observer)).2
    have ht := (abs_le.mp (hbase observer (positive r))).1
    have := mul_le_mul_of_nonneg_left ht ha
    nlinarith
  have hearly : -(1 + a) * (∑ s ∈ Finset.range r, mass s) ≤
      ∑ s ∈ Finset.range r,
        (a * pulse (mass s) (positive s) (negative s) (positive r) -
          pulse (mass s) (positive s) (negative s) observer) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    exact weighted_pulse_lower a (mass s) (positive s) (negative s)
      observer (positive r) ha (hmass s (lt_trans (Finset.mem_range.mp hs) hr))
  have hlast := separated_weighted_gain a (mass r) (positive r) (negative r)
    observer (hmass r hr) hseparated hobserver
  have hidentity :
      a * perturbed base mass positive negative L observer (positive r) -
        perturbed base mass positive negative L observer observer =
      (a * base observer (positive r) - base observer observer) +
        ∑ s ∈ Finset.range L,
          (a * pulse (mass s) (positive s) (negative s) (positive r) -
            pulse (mass s) (positive s) (negative s) observer) := by
    simp only [perturbed, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hpositive : ε < a * perturbed base mass positive negative L observer (positive r) -
      perturbed base mass positive negative L observer observer := by
    rw [hidentity, weighted_sum_at_last a mass positive negative L r observer (positive r) hr hlater]
    nlinarith
  linarith

theorem correct_perturbation_implies_agreement [Nontrivial Agent]
    (a ε : ℝ) (base : Agent → Agent → ℝ) (mass : ℕ → ℝ)
    (positive negative : ℕ → Agent) (L : ℕ) (T : ℝ)
    (ha : 0 ≤ a) (hbase : ∀ i j, |base i j| ≤ T)
    (hmass : ∀ r < L, 0 ≤ mass r)
    (hlarge : ∀ r < L,
      (1 + a) * (T + ∑ s ∈ Finset.range r, mass s) + ε < a * mass r)
    (hcorrect : RelaxedEF (perturbed base mass positive negative L) a ε) :
    RelaxedEF base a ε ∧ ∀ r < L, positive r = negative r := by
  classical
  have hagrees : ∀ r < L, positive r = negative r := by
    by_contra hn
    push Not at hn
    obtain ⟨r, hr, hsep, hlater⟩ := exists_largest_separated positive negative L hn
    obtain ⟨i, hi⟩ := exists_ne (positive r)
    have hfail := last_separated_forces_failure a ε base mass positive negative
      L r T i ha hbase hmass hr hsep hlater hi (hlarge r hr)
    exact (not_lt_of_ge (hcorrect i (positive r))) hfail
  refine ⟨?_, hagrees⟩
  rwa [all_coassigned_preserves_values base mass positive negative L hagrees] at hcorrect


/-- The explicit pulse mass used in the full proof is positive and satisfies
both the additive and multiplicative comparison requirement. -/
theorem explicit_mass_suffices {a T S ε : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε) :
    0 < (2 / a) * (T + S + ε + 1) ∧
      (1 + a) * (T + S) + ε < a * ((2 / a) * (T + S + ε + 1)) := by
  have hmass : 0 < (2 / a) * (T + S + ε + 1) := by positivity
  have hid : a * ((2 / a) * (T + S + ε + 1)) =
      2 * (T + S + ε + 1) := by field_simp
  have hbound := mul_le_mul_of_nonneg_right ha1 (add_nonneg hT hS)
  constructor
  · exact hmass
  · rw [hid]
    nlinarith

/-- The ownership-discrepancy budget remains positive throughout the full
parameter range asserted by the mixed theorem. -/
theorem discrepancy_budget_positive {a ε : ℝ} (h : ε < a) :
    0 < (a - ε) / 4 := by linarith


/-- Relative envy is meaningful even when either compared value is negative
or zero; it uses no normalization by the whole-resource value. -/
def RelativeEF (value : Agent → Agent → ℝ) (a : ℝ) : Prop :=
  ∀ i j, value i j - value i i ≤
    (1 - a) * max |value i i| |value i j|

theorem relative_comparison_nonnegative {a x y : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y - x ≤ (1 - a) * max |x| |y| ↔ a * y ≤ x := by
  rw [abs_of_nonneg hx, abs_of_nonneg hy]
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy]
    constructor <;> intro h <;> nlinarith
  · rw [max_eq_left hyx]
    constructor
    · intro _
      have hprod := mul_le_mul_of_nonneg_right ha1 hy
      nlinarith
    · intro _
      have hprod := mul_nonneg (sub_nonneg.mpr ha1) hx
      linarith

theorem positive_other_forces_positive_own {a x y : ℝ}
    (ha : 0 < a) (hy : 0 < y)
    (hrel : y - x ≤ (1 - a) * max |x| |y|) : 0 < x := by
  by_contra hn
  have hx : x ≤ 0 := le_of_not_gt hn
  rw [abs_of_nonpos hx, abs_of_pos hy] at hrel
  rcases le_total (-x) y with hxy | hyx
  · rw [max_eq_right hxy] at hrel
    have hprod := mul_pos ha hy
    nlinarith
  · rw [max_eq_left hyx] at hrel
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha.le hx
    nlinarith

theorem relative_comparison_nonnegative_own {a x y : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    y - x ≤ (1 - a) * max |x| |y| ↔ a * y ≤ x := by
  by_cases hy : 0 ≤ y
  · exact relative_comparison_nonnegative ha ha1 hx hy
  · have hy0 : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    have hmax : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
    constructor
    · intro _
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos ha hy0) hx
    · intro _
      have hprod := mul_nonneg (sub_nonneg.mpr ha1) hmax
      linarith

theorem exact_ef_implies_relative (value : Agent → Agent → ℝ) (a : ℝ)
    (ha1 : a ≤ 1) (hef : ∀ i j, value i j ≤ value i i) :
    RelativeEF value a := by
  intro i j
  have hmax : 0 ≤ max |value i i| |value i j| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have hprod := mul_nonneg (sub_nonneg.mpr ha1) hmax
  have hcomp := hef i j
  linarith

/-- Actual finite utility rows with positive totals satisfy exactly the same
multiplicative predicate under the signed relative definition and the usual
cake formula. This is the reduction used by the mixed impossibility proof. -/
theorem relative_iff_cake_comparisons [Fintype Agent]
    (value : Agent → Agent → ℝ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (htotal : ∀ i, 0 < ∑ j, value i j) :
    RelativeEF value a ↔ RelaxedEF value a 0 := by
  classical
  have existsPos (i : Agent) : ∃ j, 0 < value i j := by
    by_contra hn
    push_neg at hn
    have hsum : (∑ j, value i j) ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
    exact (not_le_of_gt (htotal i)) hsum
  constructor
  · intro hrel i j
    obtain ⟨k, hk⟩ := existsPos i
    have hown := positive_other_forces_positive_own ha hk (hrel i k)
    have hcomp := (relative_comparison_nonnegative_own ha.le ha1 hown.le).mp (hrel i j)
    linarith
  · intro hlinear i j
    obtain ⟨k, hk⟩ := existsPos i
    have hprod := mul_pos ha hk
    have hcomp := hlinear i k
    have hown : 0 < value i i := by linarith
    apply (relative_comparison_nonnegative_own ha.le ha1 hown.le).mpr
    have hcomp' := hlinear i j
    linarith

end EnvyFreeResearch.MixedApproximation
