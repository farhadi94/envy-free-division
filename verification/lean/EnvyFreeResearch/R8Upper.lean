import Mathlib

/-! Finite random-order moments and actual-source selection inequalities for Round 8.
The continuous sampling and physical allocation claims remain in the author note. -/

namespace EnvyFreeResearch.R8Upper

open scoped BigOperators

section MarkedPermutations

variable {N : ℕ}

/-- A witness is included precisely when it precedes the threshold marker. -/
def beforeMarker (rho : Equiv.Perm (Fin N)) (a marker : Fin N) : ℝ :=
  if rho a < rho marker then 1 else 0

/-- The designated label is last among these three labels. -/
def lastOfThree (rho : Equiv.Perm (Fin N)) (a b c : Fin N) : ℝ :=
  if rho a < rho c ∧ rho b < rho c then 1 else 0

noncomputable def permutationMean (f : Equiv.Perm (Fin N) → ℝ) : ℝ :=
  (∑ rho, f rho) / Fintype.card (Equiv.Perm (Fin N))

theorem permutation_count_pos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin N)))

theorem permutation_mean_const (c : ℝ) : permutationMean (fun _ : Equiv.Perm (Fin N) => c) = c := by
  unfold permutationMean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (ne_of_gt permutation_count_pos)

theorem permutation_mean_add (f g : Equiv.Perm (Fin N) → ℝ) :
    permutationMean (fun rho => f rho + g rho) = permutationMean f + permutationMean g := by
  simp only [permutationMean, Finset.sum_add_distrib, add_div]

theorem permutation_mean_sub (f g : Equiv.Perm (Fin N) → ℝ) :
    permutationMean (fun rho => f rho - g rho) = permutationMean f - permutationMean g := by
  simp only [permutationMean, Finset.sum_sub_distrib, sub_div]

theorem permutation_mean_smul (c : ℝ) (f : Equiv.Perm (Fin N) → ℝ) :
    permutationMean (fun rho => c * f rho) = c * permutationMean f := by
  simp only [permutationMean, ← Finset.mul_sum]
  ring

theorem permutation_mean_relabel (tau : Equiv.Perm (Fin N))
    (f : Equiv.Perm (Fin N) → ℝ) :
    permutationMean (fun rho => f (rho * tau)) = permutationMean f := by
  unfold permutationMean
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight tau) f

theorem before_marker_swap (rho : Equiv.Perm (Fin N)) (a marker : Fin N)
    (h : a ≠ marker) :
    beforeMarker (rho * Equiv.swap a marker) a marker = 1 - beforeMarker rho a marker := by
  have hn : rho a ≠ rho marker := rho.injective.ne h
  simp only [beforeMarker, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rcases lt_trichotomy (rho a) (rho marker) with hlt | heq | hgt
  · simp [hlt, not_lt_of_gt hlt]
  · exact False.elim (hn heq)
  · simp [hgt, not_lt_of_gt hgt]

/-- The actual finite uniform permutation law includes each witness with probability one half. -/
theorem before_marker_mean (a marker : Fin N) (h : a ≠ marker) :
    permutationMean (fun rho => beforeMarker rho a marker) = 1 / 2 := by
  have hs := permutation_mean_relabel (Equiv.swap a marker)
    (fun rho => beforeMarker rho a marker)
  simp_rw [before_marker_swap _ _ _ h] at hs
  rw [permutation_mean_sub, permutation_mean_const] at hs
  linarith

theorem last_three_partition (rho : Equiv.Perm (Fin N)) (a b c : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    lastOfThree rho a b c + lastOfThree rho c b a + lastOfThree rho a c b = 1 := by
  have hab' := rho.injective.ne hab
  have hac' := rho.injective.ne hac
  have hbc' := rho.injective.ne hbc
  simp only [lastOfThree]
  split_ifs <;> norm_num <;> omega

theorem last_three_swap_first (rho : Equiv.Perm (Fin N)) (a b c : Fin N)
    (hab : a ≠ b) (hbc : b ≠ c) :
    lastOfThree (rho * Equiv.swap a c) a b c = lastOfThree rho c b a := by
  simp only [lastOfThree, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]

theorem last_three_swap_second (rho : Equiv.Perm (Fin N)) (a b c : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) :
    lastOfThree (rho * Equiv.swap b c) a b c = lastOfThree rho a c b := by
  simp only [lastOfThree, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab hac]

/-- Of three distinct labels, each is the last with probability one third. -/
theorem last_three_mean (a b c : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permutationMean (fun rho => lastOfThree rho a b c) = 1 / 3 := by
  have hfirst := permutation_mean_relabel (Equiv.swap a c)
    (fun rho => lastOfThree rho a b c)
  simp_rw [last_three_swap_first _ _ _ _ hab hbc] at hfirst
  have hsecond := permutation_mean_relabel (Equiv.swap b c)
    (fun rho => lastOfThree rho a b c)
  simp_rw [last_three_swap_second _ _ _ _ hab hac] at hsecond
  have hp : permutationMean (fun rho => lastOfThree rho a b c +
      lastOfThree rho c b a + lastOfThree rho a c b) = 1 := by
    simp_rw [last_three_partition _ _ _ _ hab hac hbc]
    exact permutation_mean_const 1
  rw [permutation_mean_add, permutation_mean_add, hfirst, hsecond] at hp
  linarith

theorem before_marker_product (rho : Equiv.Perm (Fin N)) (a b marker : Fin N) :
    beforeMarker rho a marker * beforeMarker rho b marker = lastOfThree rho a b marker := by
  simp only [beforeMarker, lastOfThree]
  split_ifs <;> norm_num <;> tauto

/-- Distinct witness inclusions have joint probability one third, from the actual permutation law. -/
theorem before_marker_pair_mean (a b marker : Fin N)
    (hab : a ≠ b) (ha : a ≠ marker) (hb : b ≠ marker) :
    permutationMean (fun rho => beforeMarker rho a marker * beforeMarker rho b marker) = 1 / 3 := by
  simp_rw [before_marker_product]
  exact last_three_mean a b marker hab ha hb

noncomputable def centeredBefore (rho : Equiv.Perm (Fin N)) (a marker : Fin N) : ℝ :=
  beforeMarker rho a marker - 1 / 2

theorem centered_before_mean (a marker : Fin N) (h : a ≠ marker) :
    permutationMean (fun rho => centeredBefore rho a marker) = 0 := by
  unfold centeredBefore
  rw [permutation_mean_sub, before_marker_mean _ _ h, permutation_mean_const]
  norm_num

theorem centered_before_square (rho : Equiv.Perm (Fin N)) (a marker : Fin N) :
    centeredBefore rho a marker ^ 2 = 1 / 4 := by
  simp only [centeredBefore, beforeMarker]
  split_ifs <;> norm_num

theorem centered_before_self_mean (a marker : Fin N) :
    permutationMean (fun rho => centeredBefore rho a marker * centeredBefore rho a marker) = 1 / 4 := by
  simp_rw [← pow_two, centered_before_square]
  exact permutation_mean_const _

theorem centered_before_cross_mean (a b marker : Fin N)
    (hab : a ≠ b) (ha : a ≠ marker) (hb : b ≠ marker) :
    permutationMean (fun rho => centeredBefore rho a marker * centeredBefore rho b marker) = 1 / 12 := by
  have heq : (fun rho => centeredBefore rho a marker * centeredBefore rho b marker) =
      (fun rho => beforeMarker rho a marker * beforeMarker rho b marker -
        (1 / 2) * beforeMarker rho a marker - (1 / 2) * beforeMarker rho b marker + (1 / 4)) := by
    funext rho
    unfold centeredBefore
    ring
  rw [heq, permutation_mean_add, permutation_mean_sub, permutation_mean_sub,
    permutation_mean_smul, permutation_mean_smul,
    before_marker_pair_mean _ _ _ hab ha hb,
    before_marker_mean _ _ ha, before_marker_mean _ _ hb, permutation_mean_const]
  norm_num

theorem centered_before_covariance (a b marker : Fin N)
    (ha : a ≠ marker) (hb : b ≠ marker) :
    permutationMean (fun rho => centeredBefore rho a marker * centeredBefore rho b marker) =
      (if a = b then 1 / 6 else 0) + 1 / 12 := by
  by_cases hab : a = b
  · subst b
    rw [centered_before_self_mean]
    norm_num
  · rw [centered_before_cross_mean _ _ _ hab ha hb]
    simp [hab]

theorem permutation_mean_sum {W : Type*} [Fintype W]
    (f : W → Equiv.Perm (Fin N) → ℝ) :
    permutationMean (fun rho => ∑ a, f a rho) = ∑ a, permutationMean (f a) := by
  unfold permutationMean
  rw [Finset.sum_comm]
  exact Finset.sum_div _ _ _

/-- Actual covariance of arbitrary real weights under the random-order/threshold law. -/
theorem random_order_covariance {W : Type*} [Fintype W]
    (label : W → Fin N) (hinj : Function.Injective label) (marker : Fin N)
    (hmark : ∀ a, label a ≠ marker) (d : W → ℝ) :
    permutationMean (fun rho => (∑ a, d a * centeredBefore rho (label a) marker) ^ 2) =
      (1 / 6) * (∑ a, d a ^ 2) + (1 / 12) * (∑ a, d a) ^ 2 := by
  classical
  have hexpand : ∀ rho : Equiv.Perm (Fin N),
      (∑ a, d a * centeredBefore rho (label a) marker) ^ 2 =
      ∑ a, ∑ b, (d a * d b) *
        (centeredBefore rho (label a) marker * centeredBefore rho (label b) marker) := by
    intro rho
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand, permutation_mean_sum, permutation_mean_smul,
    centered_before_covariance _ _ _ (hmark _) (hmark _)]
  have hlabel : ∀ a b, label a = label b ↔ a = b := fun a b => hinj.eq_iff
  simp_rw [hlabel, mul_add, Finset.sum_add_distrib]
  have hdiag : (∑ a, ∑ b, d a * d b * (if a = b then (1 / 6 : ℝ) else 0)) =
      (1 / 6) * ∑ a, d a ^ 2 := by
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hall : (∑ a, ∑ b, d a * d b * (1 / 12 : ℝ)) =
      (1 / 12) * (∑ a, d a) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hdiag, hall]

theorem random_order_weighted_mean {W : Type*} [Fintype W]
    (label : W → Fin N) (marker : Fin N) (hmark : ∀ a, label a ≠ marker) (d : W → ℝ) :
    permutationMean (fun rho => ∑ a, d a * beforeMarker rho (label a) marker) =
      (1 / 2) * ∑ a, d a := by
  simp_rw [permutation_mean_sum, permutation_mean_smul, before_marker_mean _ _ (hmark _)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

/-- The designated increments provide the exact L(L+2)/108 lower bound. -/
theorem designated_variance_lower {W : Type*} [Fintype W]
    (d : W → ℝ) (A : ℝ) (hA : 0 ≤ A) (hd : ∀ a, A / 3 ≤ d a) :
    A ^ 2 * (Fintype.card W : ℝ) * ((Fintype.card W : ℝ) + 2) / 108 ≤
      (1 / 6) * (∑ a, d a ^ 2) + (1 / 12) * (∑ a, d a) ^ 2 := by
  have hc : (0 : ℝ) ≤ Fintype.card W := by positivity
  have hdsq : ∀ a, A ^ 2 / 9 ≤ d a ^ 2 := by
    intro a
    have ha := hd a
    nlinarith [sq_nonneg (d a - A / 3)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hd a)
  have hs2 := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hdsq a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs hs2
  have hsnon : 0 ≤ ∑ a, d a := le_trans (mul_nonneg hc (div_nonneg hA (by norm_num))) hs
  have hsquare : ((Fintype.card W : ℝ) * (A / 3)) ^ 2 ≤ (∑ a, d a) ^ 2 :=
    sq_le_sq₀ (mul_nonneg hc (div_nonneg hA (by norm_num))) hsnon |>.mpr hs
  nlinarith

/-- The variance bound is instantiated on the actual marked-permutation outcomes. -/
theorem random_order_designated_variance {W : Type*} [Fintype W]
    (label : W → Fin N) (hinj : Function.Injective label) (marker : Fin N)
    (hmark : ∀ a, label a ≠ marker) (d : W → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hd : ∀ a, A / 3 ≤ d a) :
    A ^ 2 * (Fintype.card W : ℝ) * ((Fintype.card W : ℝ) + 2) / 108 ≤
      permutationMean (fun rho => (∑ a, d a * centeredBefore rho (label a) marker) ^ 2) := by
  rw [random_order_covariance label hinj marker hmark d]
  exact designated_variance_lower d A hA hd

/-- An opposite-sign two-witness spike has variance one third under actual random ordering. -/
theorem opposite_witness_spike_second_moment (a b marker : Fin N)
    (hab : a ≠ b) (ha : a ≠ marker) (hb : b ≠ marker) :
    permutationMean (fun rho => (beforeMarker rho a marker - beforeMarker rho b marker) ^ 2) = 1 / 3 := by
  have hexpand : (fun rho => (beforeMarker rho a marker - beforeMarker rho b marker) ^ 2) =
      (fun rho => centeredBefore rho a marker * centeredBefore rho a marker +
        centeredBefore rho b marker * centeredBefore rho b marker -
        2 * (centeredBefore rho a marker * centeredBefore rho b marker)) := by
    funext rho
    unfold centeredBefore
    ring
  rw [hexpand, permutation_mean_sub, permutation_mean_add, permutation_mean_smul,
    centered_before_self_mean, centered_before_self_mean,
    centered_before_cross_mean _ _ _ hab ha hb]
  norm_num

/-- The centered threshold count is uncorrelated with an opposite-sign two-witness spike. -/
theorem threshold_count_spike_covariance {W : Type*} [Fintype W]
    (label : W → Fin N) (hinj : Function.Injective label) (marker : Fin N)
    (hmark : ∀ a, label a ≠ marker) (p n : W) :
    permutationMean (fun rho => (∑ a, centeredBefore rho (label a) marker) *
      (beforeMarker rho (label p) marker - beforeMarker rho (label n) marker)) = 0 := by
  classical
  have hexpand : ∀ rho : Equiv.Perm (Fin N),
      (∑ a, centeredBefore rho (label a) marker) *
      (beforeMarker rho (label p) marker - beforeMarker rho (label n) marker) =
      (∑ a, centeredBefore rho (label a) marker * centeredBefore rho (label p) marker) -
      (∑ a, centeredBefore rho (label a) marker * centeredBefore rho (label n) marker) := by
    intro rho
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← mul_sub]
    congr 1
    unfold centeredBefore
    ring
  simp_rw [hexpand, permutation_mean_sub, permutation_mean_sum,
    centered_before_covariance _ _ _ (hmark _) (hmark _), hinj.eq_iff]
  simp [Finset.sum_add_distrib]

/-- Arithmetic part of the conditional equal-bit probability, including every threshold. -/
theorem equal_bit_probability_lower (L t : ℝ) (hL : 4 ≤ L) :
    (1 / 3 : ℝ) ≤ (t * (t - 1) + (L - t) * (L - t - 1)) / (L * (L - 1)) := by
  have hden : 0 < L * (L - 1) := mul_pos (by linarith) (by linarith)
  apply (le_div_iff₀ hden).mpr
  nlinarith [sq_nonneg (2 * t - L), mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ L - 4)]

end MarkedPermutations

section ActualSourceScalars

noncomputable def leftDensity (epsilon : ℝ) : ℝ := 1 + epsilon / (1 / 2 - epsilon)

noncomputable def rightDensity (epsilon : ℝ) : ℝ := 1 - epsilon

/-- Normalization identity for the three-interval density fixture. -/
theorem fixture_density_total (epsilon : ℝ) (he : epsilon < 1 / 2) :
    leftDensity epsilon * (1 / 2 - epsilon) + (1 / 2) * epsilon +
      rightDensity epsilon * (1 / 2) = 1 := by
  have hn : (1 / 2 : ℝ) - epsilon ≠ 0 := ne_of_gt (by linarith)
  have hleft : leftDensity epsilon * (1 / 2 - epsilon) = 1 / 2 := by
    unfold leftDensity
    rw [add_mul, one_mul, div_mul_cancel₀ _ hn]
    ring
  rw [hleft]
  unfold rightDensity
  ring

theorem fixture_density_bounds (epsilon : ℝ) (he0 : 0 < epsilon)
    (he : epsilon ≤ 1 / 10) :
    1 ≤ leftDensity epsilon ∧ leftDensity epsilon ≤ 5 / 4 ∧
      9 / 10 ≤ rightDensity epsilon ∧ rightDensity epsilon ≤ 1 ∧
      leftDensity epsilon - rightDensity epsilon ≤ (7 / 2) * epsilon := by
  have hd : 0 < (1 / 2 : ℝ) - epsilon := by linarith
  have hratio : epsilon / (1 / 2 - epsilon) ≤ (5 / 2) * epsilon := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg he0.le (show 0 ≤ 1 / 10 - epsilon by linarith)]
  have hratio' : epsilon / (1 / 2 - epsilon) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hratio0 : 0 ≤ epsilon / (1 / 2 - epsilon) := div_nonneg he0.le hd.le
  unfold leftDensity rightDensity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Any maximum of a normalized finite row is too large to be the tiny exceptional cell. -/
theorem maximum_cell_avoids_exception {Cell : Type*} [Fintype Cell]
    (x : Cell → ℝ) (chosen special : Cell) (m epsilon : ℝ)
    (hm : 0 < m) (hcard : (Fintype.card Cell : ℝ) ≤ 2 * m)
    (htotal : ∑ e, x e = 1) (hmax : ∀ e, x e ≤ x chosen)
    (hsmall : epsilon < 1 / (2 * m)) (hspecial : x special = epsilon) :
    1 / (2 * m) ≤ x chosen ∧ chosen ≠ special := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hmax e)
  simp only [htotal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hnon : 0 ≤ x chosen := by
    by_contra hn
    have hc : (0 : ℝ) ≤ Fintype.card Cell := by positivity
    have hmul := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge hn)
    linarith
  have hprod : 1 ≤ (2 * m) * x chosen :=
    le_trans hsum (mul_le_mul_of_nonneg_right hcard hnon)
  have hbound : 1 / (2 * m) ≤ x chosen := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * m)).mpr
    nlinarith
  refine ⟨hbound, ?_⟩
  intro heq
  rw [heq, hspecial] at hbound
  linarith

/-- The outside-cell residual is uniformly smaller than the exceptional residual. -/
theorem fixture_outside_residual (epsilon eta x s r : ℝ)
    (he0 : 0 < epsilon) (he : epsilon ≤ 1 / 10) (heta : eta ≤ 1 / 20)
    (hx0 : 0 ≤ x) (hx : x ≤ eta)
    (hs : rightDensity epsilon ≤ s ∧ s ≤ leftDensity epsilon)
    (hr : rightDensity epsilon ≤ r ∧ r ≤ leftDensity epsilon) :
    |s * x - r * x| ≤ (7 / 40) * epsilon := by
  obtain ⟨_, _, _, _, hgap⟩ := fixture_density_bounds epsilon he0 he
  have habs : |s - r| ≤ leftDensity epsilon - rightDensity epsilon :=
    abs_le.mpr ⟨by linarith [hs.1, hr.2], by linarith [hs.2, hr.1]⟩
  have hid : |s * x - r * x| = |s - r| * x := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hx0]
  rw [hid]
  calc
    |s - r| * x ≤ ((7 / 2) * epsilon) * eta :=
      mul_le_mul (le_trans habs hgap) hx hx0 (by positivity)
    _ ≤ (7 / 40) * epsilon := by nlinarith

theorem fixture_exception_residual (epsilon r : ℝ)
    (he0 : 0 < epsilon) (he : epsilon ≤ 1 / 10)
    (hr : rightDensity epsilon ≤ r) :
    (2 / 5) * epsilon ≤ |(1 / 2) * epsilon - r * epsilon| := by
  obtain ⟨_, _, hd, _, _⟩ := fixture_density_bounds epsilon he0 he
  have h : (2 / 5) * epsilon ≤ -((1 / 2) * epsilon - r * epsilon) := by
    nlinarith
  exact le_trans h (neg_le_abs _)

/-- The actual second representative is unique, independent of ties in the first. -/
theorem fixture_unique_second_representative {Cell : Type*}
    (x y : Cell → ℝ) (special : Cell) (epsilon eta r : ℝ)
    (he0 : 0 < epsilon) (he : epsilon ≤ 1 / 10) (heta : eta ≤ 1 / 20)
    (hr : rightDensity epsilon ≤ r ∧ r ≤ leftDensity epsilon)
    (hxE : x special = epsilon) (hyE : y special = (1 / 2) * epsilon)
    (hout : ∀ e, e ≠ special → 0 ≤ x e ∧ x e ≤ eta ∧
      ∃ s, rightDensity epsilon ≤ s ∧ s ≤ leftDensity epsilon ∧ y e = s * x e) :
    ∀ e, e ≠ special → |y e - r * x e| < |y special - r * x special| := by
  intro e hne
  obtain ⟨hx0, hx, s, hs0, hs1, hy⟩ := hout e hne
  have hout' := fixture_outside_residual epsilon eta (x e) s r he0 he heta hx0 hx
    ⟨hs0, hs1⟩ hr
  have hspecial := fixture_exception_residual epsilon r he0 he hr.1
  rw [hxE, hyE, hy]
  linarith

/-- Reserve normalization leaves the exceptional representative uniformly separated. -/
theorem fixture_normalized_exception (epsilon t : ℝ) (he0 : 0 < epsilon)
    (ht : (9 / 10 : ℝ) ≤ t) :
    (4 / 9) * epsilon ≤ |epsilon - ((1 / 2) * epsilon) / t| := by
  have ht0 : 0 < t := by linarith
  have hdiv : ((1 / 2) * epsilon) / t ≤ (5 / 9) * epsilon := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith
  exact le_trans (by linarith : (4 / 9) * epsilon ≤ epsilon - ((1 / 2) * epsilon) / t)
    (le_abs_self _)

theorem fixture_normalized_outside (epsilon eta x s t : ℝ)
    (he0 : 0 < epsilon) (he : epsilon ≤ 1 / 10) (heta : eta ≤ 1 / 20)
    (hx0 : 0 ≤ x) (hx : x ≤ eta)
    (hs : rightDensity epsilon ≤ s ∧ s ≤ leftDensity epsilon)
    (ht : rightDensity epsilon ≤ t ∧ t ≤ leftDensity epsilon) :
    |x - (s * x) / t| ≤ (7 / 36) * epsilon := by
  obtain ⟨_, _, hd, _, hgap⟩ := fixture_density_bounds epsilon he0 he
  have ht9 : (9 / 10 : ℝ) ≤ t := le_trans hd ht.1
  have ht0 : 0 < t := by linarith
  have habs : |t - s| ≤ (7 / 2) * epsilon := by
    apply le_trans _ hgap
    exact abs_le.mpr ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
  have hid : x - (s * x) / t = (t - s) * x / t := by
    field_simp
  rw [hid, abs_div, abs_mul, abs_of_nonneg hx0, abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  have hbound : |t - s| * x ≤ ((7 / 2) * epsilon) * eta :=
    mul_le_mul habs hx hx0 (by positivity)
  have hsmall : ((7 / 2) * epsilon) * eta ≤ (7 / 40) * epsilon := by nlinarith
  have hlast : (7 / 40) * epsilon ≤ ((7 / 36) * epsilon) * t := by nlinarith
  exact le_trans hbound (le_trans hsmall hlast)

/-- Restriction to the tiny selected cell forces an inverse-mass endpoint law. -/
theorem selected_cell_domination_cost (epsilon Lambda : ℝ) (he : 0 < epsilon)
    (hdom : 2 ≤ Lambda * ((5 / 6) * epsilon)) :
    12 / (5 * epsilon) ≤ Lambda := by
  apply (div_le_iff₀ (by positivity : 0 < 5 * epsilon)).mpr
  nlinarith

/-- The two-endpoint charge is not controlled by endpoint count alone. -/
theorem zero_recorded_scale_endpoint_charge (e₁ e₂ : ℝ) (h₁ : 0 < e₁) (h₂ : 0 < e₂) :
    e₁ / (0 + e₁) + e₂ / (0 + e₂) = 2 := by
  norm_num [ne_of_gt h₁, ne_of_gt h₂]

end ActualSourceScalars

end EnvyFreeResearch.R8Upper
