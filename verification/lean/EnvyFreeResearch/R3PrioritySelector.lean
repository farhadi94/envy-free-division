import Mathlib

/-!
Finite certificates for the rational-profile priority-selector adversary.
The countable family, measure construction, oracle replay, and probability
argument are not formalized here. The main new finite ingredient is that
arbitrarily large integer pulse masses avoid finitely many affine zeros.
-/

namespace RealRandomMixedFinite

open scoped BigOperators

theorem large_integer_avoids_affine_zeros {Index : Type*}
    (s : Finset Index) (offset slope : Index → ℝ)
    (hoffset : ∀ j ∈ s, offset j ≠ 0) (lower : ℝ) :
    ∃ mass : ℕ, lower < (mass : ℝ) ∧
      ∀ j ∈ s, offset j + slope j * (mass : ℝ) ≠ 0 := by
  classical
  let total : ℝ := ∑ j ∈ s, |offset j / slope j|
  have htotal : 0 ≤ total := Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨mass, hmass⟩ := exists_nat_gt (|lower| + total + 1)
  refine ⟨mass, ?_, ?_⟩
  · linarith [le_abs_self lower]
  · intro j hj hzero
    by_cases hslope : slope j = 0
    · simp only [hslope, zero_mul, add_zero] at hzero
      exact hoffset j hj hzero
    · have hroot : (mass : ℝ) = -offset j / slope j := by
        apply (eq_div_iff hslope).mpr
        nlinarith
      have hterm : |offset j / slope j| ≤ total := by
        exact Finset.single_le_sum (fun k _ => abs_nonneg (offset k / slope k)) hj
      have hnonneg : 0 ≤ (mass : ℝ) := Nat.cast_nonneg mass
      have habs : (mass : ℝ) = |offset j / slope j| := by
        calc
          (mass : ℝ) = |(mass : ℝ)| := (abs_of_nonneg hnonneg).symm
          _ = |offset j / slope j| := by rw [hroot, neg_div, abs_neg]
      linarith [abs_nonneg lower]

theorem forced_split_with_slack
    (parent outside total left u v : ℝ) (ownsRight : Bool)
    (hparent : parent - total ≤ outside)
    (hleft : outside + total ≤ left)
    (houtside : -outside ≤ u - v) :
    parent - left ≤ 0 ∧
      total ≤ (left + u) - (v + if ownsRight then parent - left else 0) := by
  have hright : parent - left ≤ 0 := by linarith
  refine ⟨hright, ?_⟩
  cases ownsRight <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem finite_priority_index_preserved
    (oldValid newValid : ℕ → Prop) (chosen : ℕ)
    (hchosen : oldValid chosen)
    (hskipped : ∀ j < chosen, ¬ oldValid j)
    (hchosenPreserved : oldValid chosen → newValid chosen)
    (hskippedPreserved : ∀ j < chosen, ¬ oldValid j → ¬ newValid j) :
    newValid chosen ∧ ∀ j < chosen, ¬ newValid j := by
  exact ⟨hchosenPreserved hchosen,
    fun j hj => hskippedPreserved j hj (hskipped j hj)⟩

#print axioms large_integer_avoids_affine_zeros
#print axioms forced_split_with_slack
#print axioms finite_priority_index_preserved

end RealRandomMixedFinite
