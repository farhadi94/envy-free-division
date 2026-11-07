import Mathlib
import EnvyFreeResearch.R5RankRefinement

/-!
# Round 6 finite upper-bound certificates

The maximum-cell envelope, finite weighted exceptional-event accounting, and
the exact common-moment support obstruction are finite statements.  No theorem
in this file asserts a continuous sampling law or implements a cut oracle.
-/

namespace EnvyFreeResearch.R6Upper

open scoped BigOperators

section MaximumCell

variable {Agent Cell : Type*} [Fintype Agent] [Nonempty Agent]
  [Fintype Cell] [Nonempty Cell]

/-- Maximum absolute disagreement on a nonempty finite table. -/
noncomputable def cellDisagreement (v : Agent → Cell → ℝ) (i j : Agent) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun e => |v i e - v j e|)

/-- Division by zero is zero; thus zero-disagreement rows contribute zero. -/
noncomputable def normalizedCell (v : Agent → Cell → ℝ) (i j : Agent)
    (e : Cell) : ℝ := |v i e - v j e| / cellDisagreement v i j

/-- A single envelope for all observers of the same recipient. -/
noncomputable def cellEnvelope (v : Agent → Cell → ℝ) (j : Agent) (e : Cell) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => normalizedCell v i j e)

omit [Fintype Agent] [Nonempty Agent] in
theorem abs_cell_le_disagreement (v : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    |v i e - v j e| ≤ cellDisagreement v i j := by
  exact Finset.le_sup' (fun a => |v i a - v j a|) (Finset.mem_univ e)

omit [Fintype Agent] [Nonempty Agent] in
theorem cell_disagreement_nonnegative (v : Agent → Cell → ℝ) (i j : Agent) :
    0 ≤ cellDisagreement v i j := by
  obtain ⟨e⟩ := ‹Nonempty Cell›
  exact (abs_nonneg _).trans (abs_cell_le_disagreement v i j e)

omit [Fintype Agent] [Nonempty Agent] in
theorem zero_cell_disagreement (v : Agent → Cell → ℝ) (i j : Agent)
    (hzero : cellDisagreement v i j = 0) : ∀ e, v i e = v j e := by
  intro e
  have h := abs_cell_le_disagreement v i j e
  rw [hzero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

omit [Fintype Agent] [Nonempty Agent] in
theorem normalized_cell_nonnegative (v : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    0 ≤ normalizedCell v i j e := by
  exact div_nonneg (abs_nonneg _) (cell_disagreement_nonnegative v i j)

omit [Fintype Agent] [Nonempty Agent] in
theorem normalized_cell_le_one (v : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    normalizedCell v i j e ≤ 1 := by
  by_cases hzero : cellDisagreement v i j = 0
  · simp [normalizedCell, hzero]
  · exact (div_le_one₀ (lt_of_le_of_ne (cell_disagreement_nonnegative v i j)
      (Ne.symm hzero))).mpr (abs_cell_le_disagreement v i j e)

theorem normalized_cell_le_envelope (v : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    normalizedCell v i j e ≤ cellEnvelope v j e := by
  exact Finset.le_sup' (fun a => normalizedCell v a j e) (Finset.mem_univ i)

theorem cell_envelope_nonnegative (v : Agent → Cell → ℝ) (j : Agent) (e : Cell) :
    0 ≤ cellEnvelope v j e := by
  exact (normalized_cell_nonnegative v j j e).trans
    (normalized_cell_le_envelope v j j e)

theorem cell_envelope_le_one (v : Agent → Cell → ℝ) (j : Agent) (e : Cell) :
    cellEnvelope v j e ≤ 1 := by
  exact Finset.sup'_le _ _ (fun i _ => normalized_cell_le_one v i j e)

theorem cell_envelope_total (v : Agent → Cell → ℝ) (j : Agent) :
    (∑ e, cellEnvelope v j e) ≤ Fintype.card Cell := by
  calc
    (∑ e, cellEnvelope v j e) ≤ ∑ _e : Cell, (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ => cell_envelope_le_one v j e)
    _ = Fintype.card Cell := by simp

omit [Fintype Agent] [Nonempty Agent] in
theorem table_variation_le_maximum (v : Agent → Cell → ℝ) (i j : Agent) :
    (∑ e, |v i e - v j e|) ≤ Fintype.card Cell * cellDisagreement v i j := by
  calc
    (∑ e, |v i e - v j e|) ≤ ∑ _e : Cell, cellDisagreement v i j :=
      Finset.sum_le_sum (fun e _ => abs_cell_le_disagreement v i j e)
    _ = Fintype.card Cell * cellDisagreement v i j := by simp

/-- This includes zero maximum disagreement and requires no union over observers. -/
theorem max_cell_weighted_error (v : Agent → Cell → ℝ) (i j : Agent)
    (z : Cell → ℝ) (hz : ∀ e, 0 ≤ z e) :
    |∑ e, z e * (v i e - v j e)| ≤
      cellDisagreement v i j * ∑ e, z e * cellEnvelope v j e := by
  by_cases hzero : cellDisagreement v i j = 0
  · simp [zero_cell_disagreement v i j hzero, hzero]
  · have hpos : 0 < cellDisagreement v i j :=
      lt_of_le_of_ne (cell_disagreement_nonnegative v i j) (Ne.symm hzero)
    have h := R5RankRefinement.weighted_coordinate_envelope
      (fun e => v i e - v j e) z (cellEnvelope v j) (cellDisagreement v i j)
      hpos hz (fun e => normalized_cell_le_envelope v i j e)
    simpa [mul_comm] using (div_le_iff₀ hpos).mp h

theorem max_cell_expected_charge {Outcome : Type*} [Fintype Outcome]
    (v : Agent → Cell → ℝ) (j : Agent) (weight : Outcome → ℝ)
    (z : Outcome → Cell → ℝ) (eps N : ℝ)
    (heps : 0 ≤ eps) (hN : (Fintype.card Cell : ℝ) ≤ N)
    (hinclusion : ∀ e, (∑ ω, weight ω * z ω e) ≤ 2 * eps) :
    (∑ ω, weight ω * ∑ e, z ω e * cellEnvelope v j e) ≤ 2 * eps * N := by
  exact R5RankRefinement.finite_expected_envelope weight z (cellEnvelope v j)
    (2 * eps) N (cell_envelope_nonnegative v j) (by positivity) hinclusion
    ((cell_envelope_total v j).trans hN)

/-- Finite weighted version of the safe, quarter-budget exceptional-event bound. -/
theorem all_recipient_exception_bound {Outcome : Type*} [Fintype Outcome]
    (v : Agent → Cell → ℝ) (weight : Outcome → ℝ)
    (z : Outcome → Agent → Cell → ℝ) (eps : Agent → ℝ) (N eta lam : ℝ)
    (hw : ∀ ω, 0 ≤ weight ω) (hz : ∀ ω j e, 0 ≤ z ω j e)
    (heps : ∀ j, 0 ≤ eps j) (hN : (Fintype.card Cell : ℝ) ≤ N)
    (heta : (∑ j, eps j) ≤ Fintype.card Agent * eta) (hlam : 0 < lam)
    (hinclusion : ∀ j e, (∑ ω, weight ω * z ω j e) ≤ 2 * eps j) :
    (∑ ω ∈ Finset.univ.filter (fun ω =>
      ∃ j, lam / 4 ≤ ∑ e, z ω j e * cellEnvelope v j e), weight ω) ≤
        8 * Fintype.card Agent * eta * N / lam := by
  classical
  let charge : Outcome → Agent → ℝ := fun ω j => ∑ e, z ω j e * cellEnvelope v j e
  have hcharge : ∀ ω j, 0 ≤ charge ω j := by
    intro ω j
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (hz ω j e)
      (cell_envelope_nonnegative v j e))
  have hNnonneg : 0 ≤ N := (Nat.cast_nonneg _).trans hN
  have hmean : (∑ ω, weight ω * ∑ j, charge ω j) ≤
      2 * (Fintype.card Agent : ℝ) * eta * N := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ ω, weight ω * charge ω j) ≤ ∑ j, 2 * eps j * N := by
        apply Finset.sum_le_sum
        intro j _
        exact max_cell_expected_charge v j weight (fun ω => z ω j) (eps j) N
          (heps j) hN (hinclusion j)
      _ = 2 * (∑ j, eps j) * N := by simp [Finset.sum_mul, Finset.mul_sum]
      _ ≤ 2 * (Fintype.card Agent : ℝ) * eta * N := by nlinarith [heta]
  calc
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => lam / 4 ≤ ∑ j, charge ω j), weight ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ω hω
        obtain ⟨_, j, hj⟩ := Finset.mem_filter.mp hω
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hj.trans ?_⟩
        exact Finset.single_le_sum (fun a _ => hcharge ω a) (Finset.mem_univ j)
      · exact fun ω _ _ => hw ω
    _ ≤ (∑ ω, weight ω * ∑ j, charge ω j) / (lam / 4) :=
      R5RankRefinement.finite_markov_bound weight (fun ω => ∑ j, charge ω j)
        (lam / 4) hw (fun ω => Finset.sum_nonneg (fun j _ => hcharge ω j))
        (by positivity)
    _ ≤ (2 * (Fintype.card Agent : ℝ) * eta * N) / (lam / 4) :=
      div_le_div_of_nonneg_right hmean (by positivity)
    _ = 8 * Fintype.card Agent * eta * N / lam := by ring

theorem row_violation_forces_envelope_violation (v : Agent → Cell → ℝ)
    (i j : Agent) (z : Cell → ℝ) (hz : ∀ e, 0 ≤ z e) (lam : ℝ)
    (hbad : lam * cellDisagreement v i j / 4 < |∑ e, z e * (v i e - v j e)|) :
    lam / 4 < ∑ e, z e * cellEnvelope v j e := by
  have herr := max_cell_weighted_error v i j z hz
  have hA := cell_disagreement_nonnegative v i j
  by_contra hnot
  have hsmall := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hsmall hA
  nlinarith

/-- The finite weighted bound applies to actual observer discrepancies. -/
theorem all_observer_error_exception_bound {Outcome : Type*} [Fintype Outcome]
    (v : Agent → Cell → ℝ) (weight : Outcome → ℝ)
    (z : Outcome → Agent → Cell → ℝ) (eps : Agent → ℝ) (N eta lam : ℝ)
    (hw : ∀ ω, 0 ≤ weight ω) (hz : ∀ ω j e, 0 ≤ z ω j e)
    (heps : ∀ j, 0 ≤ eps j) (hN : (Fintype.card Cell : ℝ) ≤ N)
    (heta : (∑ j, eps j) ≤ Fintype.card Agent * eta) (hlam : 0 < lam)
    (hinclusion : ∀ j e, (∑ ω, weight ω * z ω j e) ≤ 2 * eps j) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ∃ i j,
      lam * cellDisagreement v i j / 4 <
        |∑ e, z ω j e * (v i e - v j e)|), weight ω) ≤
          8 * Fintype.card Agent * eta * N / lam := by
  classical
  refine le_trans ?_ (all_recipient_exception_bound v weight z eps N eta lam
    hw hz heps hN heta hlam hinclusion)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    obtain ⟨_, i, j, hij⟩ := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j,
      (row_violation_forces_envelope_violation v i j (z ω j) (hz ω j) lam hij).le⟩
  · exact fun ω _ _ => hw ω

/-- Three actual error terms fit the quarter/quarter/half budget. -/
theorem quarter_quarter_half_error (whole estimate interpolation lam A : ℝ)
    (hwhole : |whole| ≤ lam * A / 2) (hestimate : |estimate| ≤ lam * A / 4)
    (hinterpolation : |interpolation| ≤ lam * A / 4) :
    |whole + estimate + interpolation| ≤ lam * A := by
  calc
    |whole + estimate + interpolation| ≤ |whole| + |estimate| + |interpolation| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le whole estimate) le_rfl)
    _ ≤ lam * A := by linarith

end MaximumCell

section PaymentObstruction

variable {TypeIndex UnitCell : Type*} [Fintype TypeIndex] [Nonempty TypeIndex]
  [DecidableEq TypeIndex] [Fintype UnitCell] [Nonempty UnitCell]

/-- The positive diagonal-plus-common-mass payment table. -/
noncomputable def paymentWeight (i h : TypeIndex) (_e : UnitCell) : ℝ :=
  (if i = h then 3 / (4 * (Fintype.card UnitCell : ℝ)) else 0) +
    1 / (4 * Fintype.card TypeIndex * Fintype.card UnitCell)

/-- `none` is the unused label; `some j` is a real recipient. -/
noncomputable def typeRecipientMass
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ) (h j : TypeIndex) : ℝ :=
  ∑ e, x h e (some j)

def paymentCellSplit (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (h : TypeIndex) (e : UnitCell) : Prop :=
  ∃ a b, a ≠ b ∧ 0 < x h e a ∧ 0 < x h e b

noncomputable def splitCells (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (h : TypeIndex) : Finset UnitCell := by
  classical
  exact Finset.univ.filter (paymentCellSplit x h)

theorem payment_weight_positive (i h : TypeIndex) (e : UnitCell) :
    0 < paymentWeight i h e := by
  have hk : (0 : ℝ) < Fintype.card TypeIndex := by exact_mod_cast Fintype.card_pos
  have hm : (0 : ℝ) < Fintype.card UnitCell := by exact_mod_cast Fintype.card_pos
  unfold paymentWeight
  split_ifs <;> positivity

theorem payment_weight_row_sum (i : TypeIndex) :
    (∑ h, ∑ e : UnitCell, paymentWeight i h e) = 1 := by
  have hk : (Fintype.card TypeIndex : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card TypeIndex ≠ 0)
  have hm : (Fintype.card UnitCell : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card UnitCell ≠ 0)
  simp [paymentWeight, Finset.sum_add_distrib]
  field_simp
  norm_num

omit [Nonempty TypeIndex] [Nonempty UnitCell] in
/-- Expanding the concrete table exposes exactly the cross-observer constraints. -/
theorem payment_moment_expansion
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ) (i j : TypeIndex) :
    (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      3 / (4 * Fintype.card UnitCell) * typeRecipientMass x i j +
      1 / (4 * Fintype.card TypeIndex * Fintype.card UnitCell) *
        ∑ h, typeRecipientMass x h j := by
  simp_rw [paymentWeight, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp [typeRecipientMass, Finset.mul_sum]
  · simp only [typeRecipientMass, Finset.mul_sum]

/-- Equal moments in the actual positive table force one half-cell of every type. -/
theorem common_moments_force_half
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) :
    ∀ h j, typeRecipientMass x h j = 1 / 2 := by
  have hk : (Fintype.card TypeIndex : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card TypeIndex ≠ 0)
  have hm : (Fintype.card UnitCell : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card UnitCell ≠ 0)
  have halpha : 3 / (4 * (Fintype.card UnitCell : ℝ)) ≠ 0 := by positivity
  have heq : ∀ i h j, typeRecipientMass x i j = typeRecipientMass x h j := by
    intro i h j
    have hi := hmoment i j
    have hh := hmoment h j
    rw [payment_moment_expansion] at hi hh
    apply mul_left_cancel₀ halpha
    linarith
  intro h j
  have hh := hmoment h j
  rw [payment_moment_expansion] at hh
  have hsum : (∑ a, typeRecipientMass x a j) =
      (Fintype.card TypeIndex : ℝ) * typeRecipientMass x h j := by
    simp_rw [heq _ h j]
    simp
  rw [hsum] at hh
  field_simp at hh
  nlinarith

theorem payment_coordinate_lt_one
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) (h j : TypeIndex) (e : UnitCell) :
    x h e (some j) < 1 := by
  have hk : (0 : ℝ) < Fintype.card TypeIndex := by exact_mod_cast Fintype.card_pos
  have hm : (0 : ℝ) < Fintype.card UnitCell := by exact_mod_cast Fintype.card_pos
  have hterm : paymentWeight h h e * x h e (some j) ≤
      1 / (2 * Fintype.card UnitCell) := by
    rw [← hmoment h j]
    apply (Finset.single_le_sum (s := Finset.univ) (a := e)
      (f := fun a => paymentWeight h h a * x h a (some j))
      (fun a _ => mul_nonneg (payment_weight_positive h h a).le (hx h a (some j)))
      (Finset.mem_univ e)).trans
    exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (payment_weight_positive h a b).le (hx a b (some j))))
      (Finset.mem_univ h)
  have hweight : 1 / (2 * (Fintype.card UnitCell : ℝ)) < paymentWeight h h e := by
    simp only [paymentWeight, ite_true]
    have hcommon : 0 < 1 / (4 * (Fintype.card TypeIndex : ℝ) *
        (Fintype.card UnitCell : ℝ)) := by positivity
    have hdiag : 1 / (2 * (Fintype.card UnitCell : ℝ)) <
        3 / (4 * (Fintype.card UnitCell : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    linarith
  by_contra hnot
  have hone : 1 ≤ x h e (some j) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hone (payment_weight_positive h h e).le
  nlinarith

omit [Nonempty TypeIndex] [DecidableEq TypeIndex] [Fintype UnitCell] [Nonempty UnitCell] in
/-- A genuinely fractional positive coordinate forces two positive labels. -/
theorem positive_fraction_implies_split
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1)
    (h : TypeIndex) (e : UnitCell) (j : TypeIndex)
    (hpos : 0 < x h e (some j)) (hlt : x h e (some j) < 1) :
    paymentCellSplit x h e := by
  classical
  by_contra hnot
  have hother : ∀ a, a ≠ some j → x h e a = 0 := by
    intro a ha
    apply le_antisymm _ (hx h e a)
    by_contra hpositive
    exact hnot ⟨some j, a, Ne.symm ha, hpos, lt_of_not_ge hpositive⟩
  have hsingle : (∑ a, x h e a) = x h e (some j) := by
    exact Finset.sum_eq_single (some j) (fun a _ ha => hother a ha) (by simp)
  linarith [hsum h e]

omit [Nonempty TypeIndex] [DecidableEq TypeIndex] [Fintype UnitCell] [Nonempty UnitCell] in
theorem real_recipient_mass_le_one
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1) (h : TypeIndex) (e : UnitCell) :
    (∑ j, x h e (some j)) ≤ 1 := by
  have hh := hsum h e
  rw [Fintype.sum_option] at hh
  linarith [hx h e none]

/-- Each type uses at least k/2 split cells under the exact moment contract. -/
theorem type_split_cell_lower_bound
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) (h : TypeIndex) :
    (Fintype.card TypeIndex : ℝ) / 2 ≤
      (splitCells x h).card := by
  classical
  have hpoint : ∀ e, (∑ j, x h e (some j)) ≤
      if paymentCellSplit x h e then (1 : ℝ) else 0 := by
    intro e
    split_ifs with hsplit
    · exact real_recipient_mass_le_one x hx hsum h e
    · have hz : ∀ j, x h e (some j) = 0 := by
        intro j
        apply le_antisymm _ (hx h e (some j))
        by_contra hpositive
        exact hsplit (positive_fraction_implies_split x hx hsum h e j
          (lt_of_not_ge hpositive) (payment_coordinate_lt_one x hx hmoment h j e))
      simp [hz]
  calc
    (Fintype.card TypeIndex : ℝ) / 2 = ∑ j, typeRecipientMass x h j := by
      simp [common_moments_force_half x hmoment, div_eq_mul_inv]
    _ = ∑ e, ∑ j, x h e (some j) := by
      unfold typeRecipientMass
      rw [Finset.sum_comm]
    _ ≤ ∑ e, if paymentCellSplit x h e then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun e _ => hpoint e)
    _ = (splitCells x h).card := by
      unfold splitCells
      simp only [← Finset.sum_filter]
      simp

/-- In integer form every type must split at least ceil(k/2) cells. -/
theorem type_split_cell_integer_lower_bound
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) (h : TypeIndex) :
    Fintype.card TypeIndex ≤ 2 * (splitCells x h).card := by
  have hb := type_split_cell_lower_bound x hx hsum hmoment h
  have hr : (Fintype.card TypeIndex : ℝ) ≤
      2 * ((splitCells x h).card : ℝ) := by linarith
  exact_mod_cast hr

/-- The concrete positive normalized table forces quadratically many split cells. -/
theorem quadratic_payment_support_obstruction
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) :
    Fintype.card TypeIndex ^ 2 ≤
      2 * ∑ h, (splitCells x h).card := by
  calc
    Fintype.card TypeIndex ^ 2 = ∑ _h : TypeIndex, Fintype.card TypeIndex := by
      simp [pow_two]
    _ ≤ ∑ h, 2 * (splitCells x h).card :=
      Finset.sum_le_sum (fun h _ => type_split_cell_integer_lower_bound x hx hsum hmoment h)
    _ = 2 * ∑ h, (splitCells x h).card := by
      rw [Finset.mul_sum]

theorem sharp_integer_payment_support_obstruction
    (x : TypeIndex → UnitCell → Option TypeIndex → ℝ)
    (hx : ∀ h e a, 0 ≤ x h e a)
    (hsum : ∀ h e, (∑ a, x h e a) = 1)
    (hmoment : ∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
      1 / (2 * Fintype.card UnitCell)) :
    Fintype.card TypeIndex * ((Fintype.card TypeIndex + 1) / 2) ≤
      ∑ h, (splitCells x h).card := by
  calc
    _ = ∑ _h : TypeIndex, (Fintype.card TypeIndex + 1) / 2 := by simp
    _ ≤ ∑ h, (splitCells x h).card := by
      apply Finset.sum_le_sum
      intro h _
      have hb := type_split_cell_integer_lower_bound x hx hsum hmoment h
      omega

omit [DecidableEq TypeIndex] [Nonempty UnitCell] in
theorem payment_target_total
    (hsize : Fintype.card UnitCell = 16 * Fintype.card TypeIndex) :
    (∑ _j : TypeIndex, (1 : ℝ) / (2 * Fintype.card UnitCell)) = 1 / 32 := by
  have hk : (Fintype.card TypeIndex : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card TypeIndex ≠ 0)
  simp [hsize]
  field_simp
  norm_num

/-- A concrete feasible plan shows the obstruction family is nonvacuous. -/
theorem positive_table_has_small_feasible_payment_plan
    (hsize : Fintype.card UnitCell = 16 * Fintype.card TypeIndex) :
    ∃ x : TypeIndex → UnitCell → Option TypeIndex → ℝ,
      (∀ h e a, 0 ≤ x h e a) ∧
      (∀ h e, (∑ a, x h e a) = 1) ∧
      (∀ i j, (∑ h, ∑ e, paymentWeight i h e * x h e (some j)) =
        1 / (2 * Fintype.card UnitCell)) := by
  have hk : (0 : ℝ) < Fintype.card TypeIndex := by exact_mod_cast Fintype.card_pos
  let x : TypeIndex → UnitCell → Option TypeIndex → ℝ :=
    fun _ _ a => match a with
      | none => 31 / 32
      | some _ => 1 / (32 * Fintype.card TypeIndex)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h e a
    cases a <;> dsimp [x] <;> positivity
  · intro h e
    rw [Fintype.sum_option]
    dsimp [x]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    norm_num
  · intro i j
    dsimp [x]
    simp_rw [← Finset.sum_mul]
    rw [payment_weight_row_sum, one_mul, hsize]
    norm_num
    ring

end PaymentObstruction

section Parameters

noncomputable def repairLambda (s : ℝ) : ℝ := s ^ 2 / 8
noncomputable def seedCount (s ell : ℝ) : ℝ := s ^ 5 * ell
noncomputable def reserveRate (s ell : ℝ) : ℝ := 1 / (s ^ 8 * ell)
noncomputable def coarseMesh (s ell : ℝ) : ℝ := 1 / (s ^ 17 * ell ^ 2)
noncomputable def sampleCount (s ell : ℝ) : ℝ := s ^ 18 * ell ^ 2
noncomputable def progressTau (s ell : ℝ) : ℝ := 1 / (4 * s ^ 10 * ell)
noncomputable def reserveTableCap (s ell : ℝ) : ℝ := 1024 * s ^ 10 * ell
noncomputable def reserveMesh (s ell : ℝ) : ℝ := 2 / (s ^ 9 * ell)
noncomputable def paymentAccuracy (s ell : ℝ) : ℝ := 1 / (32768 * s ^ 8 * ell)
noncomputable def snapshotTheta (s ell : ℝ) : ℝ := 1 / (3072 * s ^ 28 * ell ^ 3)

theorem sample_mesh_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    coarseMesh s ell * sampleCount s ell = s := by
  unfold coarseMesh sampleCount
  field_simp

theorem reserve_accuracy_sample_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    reserveRate s ell * paymentAccuracy s ell * sampleCount s ell = s ^ 2 / 32768 := by
  unfold reserveRate paymentAccuracy sampleCount
  field_simp

theorem reserve_table_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    reserveTableCap s ell = 1024 * reserveRate s ell * sampleCount s ell := by
  unfold reserveTableCap reserveRate sampleCount
  field_simp

theorem reserve_mesh_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    reserveMesh s ell = 2 * coarseMesh s ell / reserveRate s ell := by
  unfold reserveMesh coarseMesh reserveRate
  field_simp

theorem payment_accuracy_identity (s ell : ℝ) :
    paymentAccuracy s ell = repairLambda s / (4 * reserveTableCap s ell) := by
  by_cases hs : s = 0
  · simp [paymentAccuracy, repairLambda, reserveTableCap, hs]
  by_cases hl : ell = 0
  · simp [paymentAccuracy, repairLambda, reserveTableCap, hl]
  unfold paymentAccuracy repairLambda reserveTableCap
  field_simp
  ring

theorem seed_mesh_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    seedCount s ell * reserveMesh s ell = 2 / s ^ 4 := by
  unfold seedCount reserveMesh
  field_simp

theorem initial_envy_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    2 * progressTau s ell / reserveRate s ell = 1 / (2 * s ^ 2) := by
  unfold progressTau reserveRate
  field_simp
  ring

theorem snapshot_accuracy_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    snapshotTheta s ell = progressTau s ell / (768 * sampleCount s ell) := by
  unfold snapshotTheta progressTau sampleCount
  field_simp
  ring

theorem correction_budget_identity (s ell k : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    8 * k * reserveMesh s ell * reserveTableCap s ell / repairLambda s =
      131072 * (k / s) := by
  unfold reserveMesh reserveTableCap repairLambda
  field_simp
  ring

theorem reserve_count_failure_identity (s ell : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    2 * reserveRate s ell * sampleCount s ell / reserveTableCap s ell = 1 / 512 := by
  unfold reserveRate sampleCount reserveTableCap
  field_simp
  ring

theorem selected_parent_failure_identity (s ell k : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    reserveRate s ell * k ^ 3 * seedCount s ell = (k / s) ^ 3 := by
  unfold reserveRate seedCount
  field_simp

theorem representative_supply_identity (s ell k : ℝ) (hs : s ≠ 0) (hl : ell ≠ 0) :
    k ^ 3 * seedCount s ell * coarseMesh s ell = k ^ 3 / (s ^ 12 * ell) := by
  unfold seedCount coarseMesh
  field_simp

theorem payment_accuracy_le_one (s ell : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell) :
    paymentAccuracy s ell ≤ 1 := by
  have hp : 1 ≤ s ^ 8 := one_le_pow₀ hs
  have hpl : 1 ≤ s ^ 8 * ell := one_le_mul_of_one_le_of_one_le hp hl
  unfold paymentAccuracy
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32768 * s ^ 8 * ell)).mpr
  nlinarith

/-- The actual aggregate endpoint expression, with all constants retained. -/
theorem interpolation_budget (s ell k : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell)
    (hk : 1 ≤ k) :
    16 * k * (k - 1) * (1 + paymentAccuracy s ell) /
      (reserveRate s ell * paymentAccuracy s ell * (sampleCount s ell + 1)) ≤
      1048576 * (k / s) ^ 2 := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hq : 0 < reserveRate s ell := by unfold reserveRate; positivity
  have hb : 0 < paymentAccuracy s ell := by unfold paymentAccuracy; positivity
  have hm : 0 < sampleCount s ell := by unfold sampleCount; positivity
  have hb1 := payment_accuracy_le_one s ell hs hl
  have hden : 0 < reserveRate s ell * paymentAccuracy s ell *
      (sampleCount s ell + 1) := by positivity
  have hbase : 0 < reserveRate s ell * paymentAccuracy s ell * sampleCount s ell := by positivity
  have hcompare : reserveRate s ell * paymentAccuracy s ell * sampleCount s ell ≤
      reserveRate s ell * paymentAccuracy s ell * (sampleCount s ell + 1) := by nlinarith
  calc
    _ ≤ 32 * k ^ 2 /
        (reserveRate s ell * paymentAccuracy s ell * (sampleCount s ell + 1)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      have hprod : 0 ≤ k * (k - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hb1 hprod]
    _ ≤ 32 * k ^ 2 / (reserveRate s ell * paymentAccuracy s ell * sampleCount s ell) :=
      div_le_div_of_nonneg_left (by positivity) hbase hcompare
    _ = 1048576 * (k / s) ^ 2 := by
      rw [reserve_accuracy_sample_identity s ell hspos.ne' hlpos.ne']
      field_simp
      ring

theorem analytic_budget_small (kap : ℝ) (hk : 0 ≤ kap)
    (hsmall : kap ≤ 1 / 1099511627776) :
    1048576 * kap ^ 2 + 131072 * kap < 1 / 512 := by
  have hsq : kap ^ 2 ≤ (1 / 1099511627776 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hk hsmall 2
  norm_num at hsq
  linarith

theorem grouped_payment_failure_small (s ell k : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell)
    (hk : 1 ≤ k) (hkap : k / s ≤ 1 / 1099511627776) :
    16 * k * (k - 1) * (1 + paymentAccuracy s ell) /
        (reserveRate s ell * paymentAccuracy s ell * (sampleCount s ell + 1)) +
      8 * k * reserveMesh s ell * reserveTableCap s ell / repairLambda s < 1 / 512 := by
  have hi := interpolation_budget s ell k hs hl hk
  rw [correction_budget_identity s ell k (by linarith) (by linarith)]
  have hsmall := analytic_budget_small (k / s) (by positivity) hkap
  linarith

theorem whole_cell_half_allowance (s k A : ℝ) (hk : 0 ≤ k)
    (hscale : 4 * k ≤ s) (hA : 0 ≤ A) :
    k ^ 2 * A ≤ repairLambda s * A / 2 := by
  have hs : 0 ≤ s := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * k) hscale 2
  unfold repairLambda
  nlinarith [mul_le_mul_of_nonneg_right hsq hA]

theorem interpolation_quarter_allowance (s ell A D : ℝ)
    (hs : 0 < s) (hl : 0 < ell) (hD : D ≤ reserveTableCap s ell * A) :
    paymentAccuracy s ell * D ≤ repairLambda s * A / 4 := by
  have hN : 0 < reserveTableCap s ell := by unfold reserveTableCap; positivity
  have hb : 0 ≤ paymentAccuracy s ell := by unfold paymentAccuracy; positivity
  calc
    paymentAccuracy s ell * D ≤ paymentAccuracy s ell * (reserveTableCap s ell * A) :=
      mul_le_mul_of_nonneg_left hD hb
    _ = repairLambda s * A / 4 := by
      rw [payment_accuracy_identity]
      field_simp

/-- A useful monomial comparison, proved before substituting parameter exponents. -/
theorem scaled_power_bound (s ell k : ℝ) (hs : 0 < s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hks : k ≤ s) (a d : ℕ) :
    k ^ a / (s ^ (a + d) * ell) ≤ 1 / s ^ d := by
  have hp := pow_le_pow_left₀ hk hks a
  have hlpos : 0 < ell := by linarith
  calc
    _ ≤ s ^ a / (s ^ (a + d) * ell) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ ≤ s ^ a / s ^ (a + d) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [pow_pos hs (a + d)])
    _ = 1 / s ^ d := by
      rw [pow_add]
      field_simp

theorem coarse_grid_fits (s ell k : ℝ) (hs : 0 < s) (hl : ell ≠ 0)
    (hk : 2 * k ≤ s) :
    2 * k ≤ coarseMesh s ell * sampleCount s ell := by
  rw [sample_mesh_identity s ell hs.ne' hl]
  exact hk

theorem representative_supply_small (s ell k : ℝ) (hs : 2 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hks : k ≤ s) :
    k ^ 3 * seedCount s ell * coarseMesh s ell < 1 / 2 := by
  have hspos : 0 < s := by linarith
  rw [representative_supply_identity s ell k hspos.ne' (by linarith)]
  have hb := scaled_power_bound s ell k hspos hl hk hks 3 9
  have hp : (2 : ℝ) ^ 9 ≤ s ^ 9 := pow_le_pow_left₀ (by norm_num) hs 9
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 9) hp
  norm_num at hinv
  simp only [one_div] at hb
  exact hb.trans_lt (hinv.trans_lt (show (1 : ℝ) / 512 < 1 / 2 by norm_num))

theorem seed_value_small (s ell k : ℝ) (hs : 0 < s) (hl : ell ≠ 0)
    (hk : 0 ≤ k) (hscale : 4 * k ≤ s) :
    k ^ 2 * seedCount s ell * reserveMesh s ell ≤ 1 / (4 * s ^ 2) := by
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * k) hscale 2
  rw [mul_assoc, seed_mesh_identity s ell hs.ne' hl]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * s ^ 2)).mpr
  field_simp
  nlinarith

theorem total_numerical_target_small (s k : ℝ) (hs : 0 < s) (hk : 0 ≤ k)
    (hscale : 16 * k ≤ s) : k ^ 2 / s ^ 2 < 1 / 16 := by
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * k) hscale 2
  apply (div_lt_iff₀ (pow_pos hs 2)).mpr
  nlinarith [sq_pos_of_pos hs]

theorem individual_payment_fits (s k : ℝ) (hk : 0 < k)
    (hscale : 16 * k ≤ s) : k / s ^ 2 < 1 / (16 * k) := by
  have hs : 0 < s := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * k) hscale 2
  apply (div_lt_div_iff₀ (pow_pos hs 2) (by positivity)).mpr
  nlinarith [sq_pos_of_pos hk]

theorem reserve_mass_failure_small (s ell k : ℝ) (hs : 4 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hks : k ≤ s) :
    4 * k * coarseMesh s ell / reserveRate s ell < 1 / 512 := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hid : 4 * k * coarseMesh s ell / reserveRate s ell =
      4 * (k / (s ^ 9 * ell)) := by
    unfold coarseMesh reserveRate
    field_simp
  rw [hid]
  have hb := scaled_power_bound s ell k hspos hl hk hks 1 8
  norm_num only [Nat.reduceAdd, pow_one] at hb
  have hp : (4 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs 8
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 ^ 8) hp
  norm_num at hinv
  simp only [one_div] at hb
  linarith

theorem selected_parent_failure_small (s ell k : ℝ) (hs : 0 < s) (hl : ell ≠ 0)
    (hk : 0 ≤ k) (hkap : k / s ≤ 1 / 1099511627776) :
    reserveRate s ell * k ^ 3 * seedCount s ell < 1 / 512 := by
  rw [selected_parent_failure_identity s ell k hs.ne' hl]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ k / s) hkap 3
  norm_num at hp
  linarith

theorem cycle_remainder_bound (s ell k : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) : k ^ 3 / (s ^ 5 * ell) ≤ (k / s) ^ 3 := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hid : k ^ 3 / (s ^ 5 * ell) = (k / s) ^ 3 / (s ^ 2 * ell) := by
    field_simp
  rw [hid]
  exact div_le_self (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs) hl)

theorem cycle_failure_small (s ell k : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hkap : k / s ≤ 1 / 1099511627776) :
    (3 / 2 : ℝ) * (k / s) ^ 3 + k ^ 3 / (s ^ 5 * ell) < 1 / 512 := by
  have hb := cycle_remainder_bound s ell k hs hl hk
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ k / s) hkap 3
  norm_num at hp
  linarith

theorem actual_cycle_expression_bound (s ell k logBound : ℝ)
    (hs : 1 ≤ s) (hl : 1 ≤ ell) (hk : 1 ≤ k)
    (hlog : 0 ≤ logBound) (hlogle : logBound ≤ ell) :
    k ^ 2 * (k - 1) * (12 * repairLambda s * logBound + 1) /
        (seedCount s ell + 1) ≤
      (3 / 2 : ℝ) * (k / s) ^ 3 + k ^ 3 / (s ^ 5 * ell) := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hlam : 0 ≤ repairLambda s := by unfold repairLambda; positivity
  have hL : 0 < seedCount s ell := by unfold seedCount; positivity
  calc
    _ ≤ k ^ 3 * (12 * repairLambda s * ell + 1) / (seedCount s ell + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ k ^ 2 * k * (12 * repairLambda s * ell + 1) := by gcongr; linarith
        _ = _ := by ring
    _ ≤ k ^ 3 * (12 * repairLambda s * ell + 1) / seedCount s ell :=
      div_le_div_of_nonneg_left (by positivity) hL (by linarith)
    _ = _ := by
      unfold repairLambda seedCount
      field_simp
      ring

theorem numerical_extra_margin_small (s ell : ℝ) (hs : 2 ≤ s) (hl : 1 ≤ ell) :
    2 * repairLambda s * reserveMesh s ell ≤ 1 / (4 * s ^ 2) := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hp : (2 : ℝ) ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (by norm_num) hs 5
  have hprod : 2 ≤ s ^ 5 * ell := by nlinarith [mul_le_mul_of_nonneg_left hl (pow_nonneg hspos.le 5)]
  calc
    _ = 1 / (2 * s ^ 2 * (s ^ 5 * ell)) := by
      unfold repairLambda reserveMesh
      field_simp
      ring
    _ ≤ 1 / (2 * s ^ 2 * 2) := one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hprod (by positivity))
    _ = _ := by ring

theorem additional_supply_small (s ell k : ℝ) (hs : 2 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hks : k ≤ s) :
    k * repairLambda s * reserveMesh s ell < 1 / 16 := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hid : k * repairLambda s * reserveMesh s ell =
      (k / (s ^ 7 * ell)) / 4 := by
    unfold repairLambda reserveMesh
    field_simp
    ring
  rw [hid]
  have hb := scaled_power_bound s ell k hspos hl hk hks 1 6
  norm_num only [Nat.reduceAdd, pow_one] at hb
  have hp : (2 : ℝ) ^ 6 ≤ s ^ 6 := pow_le_pow_left₀ (by norm_num) hs 6
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 6) hp
  norm_num at hinv
  simp only [one_div] at hb
  linarith

theorem physical_quarter_buffer_small (s ell k : ℝ) (hs : 2 ≤ s) (hl : 1 ≤ ell)
    (hk : 0 ≤ k) (hks : k ≤ s) :
    k ^ 3 * seedCount s ell * coarseMesh s ell + 3 * reserveRate s ell / 2 < 1 / 4 := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  rw [representative_supply_identity s ell k hspos.ne' hlpos.ne']
  have hrep := scaled_power_bound s ell k hspos hl hk hks 3 9
  have hp9 : (2 : ℝ) ^ 9 ≤ s ^ 9 := pow_le_pow_left₀ (by norm_num) hs 9
  have hi9 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 9) hp9
  have hp8 : (2 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs 8
  have hden : (2 : ℝ) ^ 8 ≤ s ^ 8 * ell :=
    hp8.trans (by nlinarith [mul_le_mul_of_nonneg_left hl (pow_nonneg hspos.le 8)])
  have hi8 : reserveRate s ell ≤ 1 / (2 : ℝ) ^ 8 :=
    one_div_le_one_div_of_le (by norm_num) hden
  norm_num at hi8 hi9
  norm_num only [Nat.reduceAdd, one_div] at hrep
  linarith

theorem progress_margin_small (s ell : ℝ) (hs : 1 ≤ s) (hl : 1 ≤ ell) :
    progressTau s ell < 3 / 4 := by
  have hp : 1 ≤ s ^ 10 := one_le_pow₀ hs
  have hprod : 1 ≤ s ^ 10 * ell := one_le_mul_of_one_le_of_one_le hp hl
  have hden : (4 : ℝ) ≤ 4 * s ^ 10 * ell := by nlinarith
  have hb : progressTau s ell ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hden
  linarith

theorem snapshot_shrink_sample_capacity (s ell k J : ℝ)
    (hs : 4 ≤ s) (hl : 1 ≤ ell) (hk : 0 ≤ k) (hks : k ≤ s)
    (hJ : J ≤ 32 * k * ell) : k ^ 3 * J ≤ sampleCount s ell := by
  have hspos : 0 < s := by linarith
  have hlpos : 0 < ell := by linarith
  have hk4 : k ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hk hks 4
  have hs14 : (4 : ℝ) ^ 14 ≤ s ^ 14 := pow_le_pow_left₀ (by norm_num) hs 14
  have hproduct : 32 ≤ s ^ 14 * ell := by
    nlinarith [mul_le_mul_of_nonneg_left hl (pow_nonneg hspos.le 14)]
  calc
    k ^ 3 * J ≤ k ^ 3 * (32 * k * ell) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 32 * k ^ 4 * ell := by ring
    _ ≤ 32 * s ^ 4 * ell := by gcongr
    _ ≤ sampleCount s ell := by
      have hm := mul_le_mul_of_nonneg_left hproduct (show 0 ≤ s ^ 4 * ell by positivity)
      unfold sampleCount
      nlinarith [show s ^ 4 * s ^ 14 = s ^ 18 by ring]

theorem population_scale_conditions (n k : ℕ) (hk : k ≤ n) :
    (4398046511104 : ℝ) ≤ 1099511627776 * (max 4 n : ℕ) ∧
    (k : ℝ) / (1099511627776 * (max 4 n : ℕ)) ≤ 1 / 1099511627776 := by
  have hfour : (4 : ℝ) ≤ (max 4 n : ℕ) := by exact_mod_cast Nat.le_max_left 4 n
  have hkn : (k : ℝ) ≤ (max 4 n : ℕ) := by
    exact_mod_cast hk.trans (Nat.le_max_right 4 n)
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) <
        1099511627776 * (max 4 n : ℕ))).mpr
    linarith

theorem scale_implies_sixteen_margin (s k : ℝ) (hs : 0 < s)
    (hkap : k / s ≤ 1 / 1099511627776) : 16 * k ≤ s := by
  have h := (div_le_iff₀ hs).mp hkap
  linarith

/-- These are counts in the caller's ledger, not a probabilistic waiting-time theorem. -/
theorem query_and_cut_polynomial_ledger (n c ell : ℝ) (hn : 1 ≤ n) :
    96 * n ^ 2 * (n - 1) * sampleCount (c * n) ell ≤
        96 * c ^ 18 * n ^ 21 * ell ^ 2 ∧
    48 * n * (n - 1) * sampleCount (c * n) ell ≤
        48 * c ^ 18 * n ^ 20 * ell ^ 2 := by
  have hsample : 0 ≤ sampleCount (c * n) ell := by unfold sampleCount; positivity
  constructor
  · calc
      _ ≤ 96 * n ^ 2 * n * sampleCount (c * n) ell := by gcongr; linarith
      _ = _ := by unfold sampleCount; ring
  · calc
      _ ≤ 48 * n * n * sampleCount (c * n) ell := by gcongr; linarith
      _ = _ := by unfold sampleCount; ring

end Parameters

end EnvyFreeResearch.R6Upper
