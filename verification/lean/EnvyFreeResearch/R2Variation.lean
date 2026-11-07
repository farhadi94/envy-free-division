import Mathlib

/-!
# Round 2: base-three variation forcing

These are finite algebraic certificates for the signed sibling adversary:
outside bundle comparisons, the forcing gap, exact variation accounting,
unchanged variation of the queried row under bracket-crossing splits, and the
recurrence/normalization consequences. The adaptive oracle adversary, finite
signed-measure realization, and impossibility theorem are not Lean statements
in this module.
-/

namespace EnvyFreeResearch.R2Variation

open scoped BigOperators

/-- Values contributed by outside atoms to one recipient's bundle. -/
def outsideValue {Atom Owner : Type*} [DecidableEq Owner]
    (s : Finset Atom) (w : Atom → ℝ) (owner : Atom → Owner) (j : Owner) : ℝ :=
  ∑ a ∈ s, if owner a = j then w a else 0

/-- One outside-variation budget suffices for a difference of two bundles.
An atom can contribute `w`, `-w`, or zero; common contributions cancel. -/
theorem outside_difference_lower_bound {Atom Owner : Type*} [DecidableEq Owner]
    (s : Finset Atom) (w : Atom → ℝ) (owner : Atom → Owner) (left observer : Owner) :
    -(∑ a ∈ s, |w a|) ≤
      outsideValue s w owner left - outsideValue s w owner observer := by
  unfold outsideValue
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro a ha
  split_ifs <;> linarith [le_abs_self (w a), neg_abs_le (w a), abs_nonneg (w a)]

/-- The row's fixed net total imposes the outside-mass constraint. -/
theorem outside_mass_constraint {Atom : Type*} (s : Finset Atom)
    (w : Atom → ℝ) (parent total : ℝ)
    (htotal : parent + ∑ a ∈ s, w a = total) :
    |total - parent| ≤ ∑ a ∈ s, |w a| := by
  have heq : total - parent = ∑ a ∈ s, w a := by linarith
  rw [heq]
  exact Finset.abs_sum_le_sum_abs _ _

theorem positive_child (outside total : ℝ)
    (houtside : 0 ≤ outside) (htotal : 0 < total) :
    0 < outside + total := by
  linarith

/-- The right sibling is nonpositive for every sign of the parent's mass. -/
theorem sibling_nonpositive (parent outside total : ℝ)
    (hconstraint : |total - parent| ≤ outside) :
    parent - (outside + total) ≤ 0 := by
  have h := (abs_le.mp hconstraint).1
  linarith

theorem split_conserves_mass (parent outside total : ℝ) :
    (outside + total) + (parent - (outside + total)) = parent := by
  ring

/-- The Boolean records whether the observing nonowner of the left child owns
the right child. It covers both possibilities without spending variation twice. -/
theorem forcing_gap (parent outside total u v : ℝ) (ownsRight : Bool)
    (hconstraint : |total - parent| ≤ outside)
    (hdifference : -outside ≤ u - v) :
    total ≤ ((outside + total) + u) -
      (v + if ownsRight then parent - (outside + total) else 0) := by
  have hn := sibling_nonpositive parent outside total hconstraint
  cases ownsRight <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

/-- The finite ownership-sum version of the forcing gap. -/
theorem ownership_forcing_gap {Atom Owner : Type*} [DecidableEq Owner]
    (s : Finset Atom) (w : Atom → ℝ) (owner : Atom → Owner)
    (left observer : Owner) (parent total : ℝ) (ownsRight : Bool)
    (htotal : parent + ∑ a ∈ s, w a = total) :
    total ≤ (((∑ a ∈ s, |w a|) + total) + outsideValue s w owner left) -
      (outsideValue s w owner observer +
        if ownsRight then parent - ((∑ a ∈ s, |w a|) + total) else 0) := by
  exact forcing_gap parent (∑ a ∈ s, |w a|) total
    (outsideValue s w owner left) (outsideValue s w owner observer) ownsRight
    (outside_mass_constraint s w parent total htotal)
    (outside_difference_lower_bound s w owner left observer)

/-- Actual bundle value after allocating the two new children, in addition
to the unchanged outside ownership map. -/
def refinedValue {Atom Owner : Type*} [DecidableEq Owner]
    (s : Finset Atom) (w : Atom → ℝ) (owner : Atom → Owner)
    (leftOwner rightOwner : Owner) (parent total : ℝ) (recipient : Owner) : ℝ :=
  outsideValue s w owner recipient +
    (if recipient = leftOwner then (∑ a ∈ s, |w a|) + total else 0) +
    (if recipient = rightOwner then parent - ((∑ a ∈ s, |w a|) + total) else 0)

/-- Every nonowner of the positive child has the forcing gap, for the actual
bundle valuation formula, whenever the two children have different owners. -/
theorem separated_owners_force_gap {Atom Owner : Type*} [DecidableEq Owner]
    (s : Finset Atom) (w : Atom → ℝ) (owner : Atom → Owner)
    (leftOwner rightOwner observer : Owner) (parent total : ℝ)
    (hseparated : leftOwner ≠ rightOwner) (hnotleft : observer ≠ leftOwner)
    (htotal : parent + ∑ a ∈ s, w a = total) :
    total ≤ refinedValue s w owner leftOwner rightOwner parent total leftOwner -
      refinedValue s w owner leftOwner rightOwner parent total observer := by
  by_cases hr : observer = rightOwner
  · have h := ownership_forcing_gap s w owner leftOwner observer parent total true htotal
    simp [refinedValue, hseparated, Ne.symm hseparated, hr] at h ⊢
    linarith
  · have h := ownership_forcing_gap s w owner leftOwner observer parent total false htotal
    simp [refinedValue, hseparated, hnotleft, hr] at h ⊢
    linarith

/-- Two distinct free observers cannot both own the left child. This states
an actual envy comparison in at least one of their refined utility rows. -/
theorem two_observer_separated_gap {Atom Agent : Type*} [DecidableEq Agent]
    (s : Finset Atom) (w : Agent → Atom → ℝ) (owner : Atom → Agent)
    (leftOwner rightOwner p q : Agent) (parent : Agent → ℝ) (total : ℝ)
    (hseparated : leftOwner ≠ rightOwner) (hpq : p ≠ q)
    (hp : parent p + ∑ a ∈ s, w p a = total)
    (hq : parent q + ∑ a ∈ s, w q a = total) :
    ∃ i, (i = p ∨ i = q) ∧
      total ≤ refinedValue s (w i) owner leftOwner rightOwner (parent i) total leftOwner -
        refinedValue s (w i) owner leftOwner rightOwner (parent i) total i := by
  by_cases hpleft : p = leftOwner
  · have hqleft : q ≠ leftOwner := by
      intro h
      exact hpq (hpleft.trans h.symm)
    exact ⟨q, Or.inr rfl,
      separated_owners_force_gap s (w q) owner leftOwner rightOwner q (parent q) total
        hseparated hqleft hq⟩
  · exact ⟨p, Or.inl rfl,
      separated_owners_force_gap s (w p) owner leftOwner rightOwner p (parent p) total
        hseparated hpleft hp⟩

/-- The exact variation after a forced split, not merely an upper estimate. -/
theorem variation_exact (parent variation total : ℝ)
    (hparent : |parent| ≤ variation) (htotal : 0 ≤ total)
    (hconstraint : |total - parent| ≤ variation - |parent|) :
    (variation - |parent|) + |variation - |parent| + total| +
        |parent - (variation - |parent| + total)| =
      3 * (variation - |parent|) + 2 * total - parent := by
  have hp : 0 ≤ variation - |parent| + total := by linarith
  have hn := sibling_nonpositive parent (variation - |parent|) total hconstraint
  rw [abs_of_nonneg hp, abs_of_nonpos hn]
  ring

theorem variation_growth (parent variation total : ℝ)
    (hparent : |parent| ≤ variation) (htotal : 0 ≤ total)
    (hconstraint : |total - parent| ≤ variation - |parent|) :
    (variation - |parent|) + |variation - |parent| + total| +
        |parent - (variation - |parent| + total)| ≤
      3 * variation + 2 * total := by
  rw [variation_exact parent variation total hparent htotal hconstraint]
  have hneg := neg_abs_le parent
  have hnonneg := abs_nonneg parent
  linarith

/-- A scalar case attaining the growth envelope: a zero-mass parent. -/
theorem variation_growth_tight_at_zero (variation total : ℝ)
    (htotal : 0 ≤ total) (hvariation : total ≤ variation) :
    variation + |variation + total| + |0 - (variation + total)| =
      3 * variation + 2 * total := by
  have h : 0 ≤ variation + total := by linarith
  rw [abs_of_nonneg h, abs_of_nonpos (by linarith : 0 - (variation + total) ≤ 0)]
  ring

/-- A same-sign split preserves absolute mass, including zero/endpoints. -/
theorem same_sign_split_variation (parent child : ℝ)
    (h : (0 ≤ child ∧ child ≤ parent) ∨ (parent ≤ child ∧ child ≤ 0)) :
    |child| + |parent - child| = |parent| := by
  rcases h with ⟨h0, ha⟩ | ⟨ha, h0⟩
  · rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ parent - child),
      abs_of_nonneg (by linarith : 0 ≤ parent)]
    ring
  · rw [abs_of_nonpos h0, abs_of_nonpos (by linarith : parent - child ≤ 0),
      abs_of_nonpos (by linarith : parent ≤ 0)]
    ring

/-- A target between adjacent prefix values fixes same-sign child masses in
the queried row; the other rows remain free. -/
theorem bracket_crossing_variation (baseValue parent target : ℝ)
    (h : (baseValue ≤ target ∧ target ≤ baseValue + parent) ∨
      (baseValue + parent ≤ target ∧ target ≤ baseValue)) :
    |target - baseValue| + |baseValue + parent - target| = |parent| := by
  have hchild : (0 ≤ target - baseValue ∧ target - baseValue ≤ parent) ∨
      (parent ≤ target - baseValue ∧ target - baseValue ≤ 0) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have heq : baseValue + parent - target = parent - (target - baseValue) := by ring
  rw [heq]
  exact same_sign_split_variation parent (target - baseValue) hchild

theorem proportional_split_variation (parent ratio : ℝ)
    (h0 : 0 ≤ ratio) (h1 : ratio ≤ 1) :
    |ratio * parent| + |(1 - ratio) * parent| = |parent| := by
  rw [abs_mul, abs_mul, abs_of_nonneg h0,
    abs_of_nonneg (by linarith : 0 ≤ 1 - ratio)]
  ring

/-- Outside positive/negative masses realize the sharp difference `-S`. -/
theorem outside_extreme_witness (parent outside total : ℝ)
    (h : |total - parent| ≤ outside) :
    0 ≤ (outside + total - parent) / 2 ∧
    0 ≤ (outside - total + parent) / 2 ∧
    (outside + total - parent) / 2 - (outside - total + parent) / 2 =
      total - parent ∧
    -((outside - total + parent) / 2) - ((outside + total - parent) / 2) =
      -outside := by
  have hab := abs_le.mp h
  constructor
  · linarith [hab.1]
  constructor
  · linarith [hab.2]
  constructor <;> ring

/-- Therefore `S+τ` is the smallest positive-child value certified by the
universal one-budget outside comparison when a third party owns its sibling. -/
theorem minimal_child_for_this_interface (child outside total : ℝ)
    (hgap : total ≤ child - outside) : outside + total ≤ child := by
  linarith

def variationEnvelope (total : ℝ) : ℕ → ℝ
  | 0 => total
  | k + 1 => 3 * variationEnvelope total k + 2 * total

theorem variationEnvelope_closed (total : ℝ) (k : ℕ) :
    variationEnvelope total k = (2 * (3 : ℝ) ^ k - 1) * total := by
  induction k with
  | zero => norm_num [variationEnvelope]
  | succ k ih =>
    simp only [variationEnvelope, ih, pow_succ]
    ring

theorem variation_recurrence_bound (T : ℕ → ℝ) (total : ℝ)
    (hzero : T 0 ≤ total)
    (hstep : ∀ k, T (k + 1) ≤ 3 * T k + 2 * total) (k : ℕ) :
    T k ≤ (2 * (3 : ℝ) ^ k - 1) * total := by
  induction k with
  | zero =>
    norm_num
    exact hzero
  | succ k ih =>
    calc
      T (k + 1) ≤ 3 * T k + 2 * total := hstep k
      _ ≤ 3 * ((2 * (3 : ℝ) ^ k - 1) * total) + 2 * total := by linarith
      _ = (2 * (3 : ℝ) ^ (k + 1) - 1) * total := by rw [pow_succ]; ring

theorem envelope_coefficient_positive (k : ℕ) : 0 < 2 * (3 : ℝ) ^ k - 1 := by
  have h : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  linarith

/-- Positive net total used to keep variation at most one through K landmarks. -/
noncomputable def normalizedThreshold (K : ℕ) : ℝ := 1 / (2 * (3 : ℝ) ^ K - 1)

theorem normalizedThreshold_positive (K : ℕ) : 0 < normalizedThreshold K := by
  exact one_div_pos.mpr (envelope_coefficient_positive K)

theorem normalizedThreshold_normalizes (K : ℕ) :
    (2 * (3 : ℝ) ^ K - 1) * normalizedThreshold K = 1 := by
  unfold normalizedThreshold
  field_simp [ne_of_gt (envelope_coefficient_positive K)]

theorem envelope_normalized_up_to (k K : ℕ) (hk : k ≤ K) :
    (2 * (3 : ℝ) ^ k - 1) * normalizedThreshold K ≤ 1 := by
  have hp : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hk
  calc
    (2 * (3 : ℝ) ^ k - 1) * normalizedThreshold K ≤
        (2 * (3 : ℝ) ^ K - 1) * normalizedThreshold K := by
      apply mul_le_mul_of_nonneg_right _ (normalizedThreshold_positive K).le
      linarith
    _ = 1 := normalizedThreshold_normalizes K

theorem normalized_variation_bound (T : ℕ → ℝ) (K k : ℕ) (hk : k ≤ K)
    (hzero : T 0 ≤ normalizedThreshold K)
    (hstep : ∀ j, T (j + 1) ≤ 3 * T j + 2 * normalizedThreshold K) :
    T k ≤ 1 := by
  exact (variation_recurrence_bound T (normalizedThreshold K) hzero hstep k).trans
    (envelope_normalized_up_to k K hk)

/-- Pure scalar equivalence. The impossibility proof supplies the premise
that a successful uniform tolerance must be at least this threshold. -/
theorem threshold_inequality_iff (K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    normalizedThreshold K ≤ epsilon ↔
      (1 + 1 / epsilon) / 2 ≤ (3 : ℝ) ^ K := by
  have hden := envelope_coefficient_positive K
  unfold normalizedThreshold
  constructor
  · intro h
    have hm : 1 ≤ epsilon * (2 * (3 : ℝ) ^ K - 1) := (div_le_iff₀ hden).mp h
    have hinv : 1 / epsilon ≤ 2 * (3 : ℝ) ^ K - 1 := by
      apply (div_le_iff₀ hepsilon).mpr
      nlinarith
    linarith
  · intro h
    have hinv : 1 / epsilon ≤ 2 * (3 : ℝ) ^ K - 1 := by linarith
    have hm := (div_le_iff₀ hepsilon).mp hinv
    apply (div_le_iff₀ hden).mpr
    nlinarith

theorem logarithmic_landmark_bound (K : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hthreshold : normalizedThreshold K ≤ epsilon) :
    Real.log ((1 + 1 / epsilon) / 2) / Real.log 3 ≤ (K : ℝ) := by
  have hx : 0 < (1 + 1 / epsilon) / 2 := by positivity
  have hp := (threshold_inequality_iff K epsilon hepsilon).mp hthreshold
  have hlog := Real.log_le_log hx hp
  rw [Real.log_pow] at hlog
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mpr hlog

#print axioms outside_difference_lower_bound
#print axioms ownership_forcing_gap
#print axioms separated_owners_force_gap
#print axioms two_observer_separated_gap
#print axioms variation_exact
#print axioms variation_growth
#print axioms bracket_crossing_variation
#print axioms variation_recurrence_bound
#print axioms normalized_variation_bound
#print axioms logarithmic_landmark_bound

end EnvyFreeResearch.R2Variation
