import EnvyFreeResearch.Full.ChoresRecords
import EnvyFreeResearch.Full.ChoresTwoAgent

/-!
# Permanent formal-record insertion using actual physical queries

The secondary-label construction preserves strict formal order for every
observer while copying the trimmer's target exactly. The physical lemma proves
that one ordinary Cut realizes every genuinely strict primary bracket and
that every legal reply lies inside it. Endpoints already in the record table
can therefore be reused without changing any previous labels.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set MeasureTheory IntervalOracle

/-- Rational labels need not be restricted to `[0,1]`. -/
def intermediateLabel (left right : ℝ × ℚ) (primary : ℝ) : ℚ :=
  if primary = left.1 then
    if primary = right.1 then (left.2 + right.2) / 2 else left.2 + 1
  else if primary = right.1 then right.2 - 1 else 0

/-- All cases of zero, one, or two tied primary coordinates are handled. -/
theorem intermediateLabel_spec (left right : ℝ × ℚ) (primary : ℝ)
    (horder : recordLT left right) (hleft : left.1 ≤ primary) (hright : primary ≤ right.1) :
    recordLT left (primary, intermediateLabel left right primary) ∧
      recordLT (primary, intermediateLabel left right primary) right := by
  by_cases hl : primary = left.1 <;> by_cases hr : primary = right.1
  · have hlabels : left.2 < right.2 := by
      rcases horder with h | h
      · exfalso; linarith
      · exact h.2
    rw [intermediateLabel, ite_eq_left hl, ite_eq_left hr]
    constructor
    · exact Or.inr ⟨hl.symm, by dsimp; linarith⟩
    · exact Or.inr ⟨hr, by dsimp; linarith⟩
  · rw [intermediateLabel, ite_eq_left hl, ite_eq_right hr]
    constructor
    · exact Or.inr ⟨hl.symm, by dsimp; linarith⟩
    · exact Or.inl (lt_of_le_of_ne hright hr)
  · rw [intermediateLabel, ite_eq_right hl, ite_eq_left hr]
    constructor
    · exact Or.inl (lt_of_le_of_ne hleft (Ne.symm hl))
    · exact Or.inr ⟨hr, by dsimp; linarith⟩
  · rw [intermediateLabel, ite_eq_right hl, ite_eq_right hr]
    exact ⟨Or.inl (lt_of_le_of_ne hleft (Ne.symm hl)), Or.inl (lt_of_le_of_ne hright hr)⟩

/-- One trimmer copies both coordinates of its existing target; all other
observers receive a rational intermediate label. No old record changes. -/
def insertedRecord {Agent : Type*} [DecidableEq Agent]
    (left right : Agent → ℝ × ℚ) (primary : Agent → ℝ)
    (trimmer : Agent) (target : ℝ × ℚ) (i : Agent) : ℝ × ℚ :=
  (primary i, if i = trimmer then target.2 else intermediateLabel (left i) (right i) (primary i))

theorem insertedRecord_preserves {Agent : Type*} [DecidableEq Agent]
    (left right : Agent → ℝ × ℚ) (primary : Agent → ℝ)
    (trimmer : Agent) (target : ℝ × ℚ)
    (horder : ∀ i, recordLT (left i) (right i))
    (hbetween : ∀ i, (left i).1 ≤ primary i ∧ primary i ≤ (right i).1)
    (htarget : primary trimmer = target.1)
    (hltarget : recordLT (left trimmer) target)
    (hrtarget : recordLT target (right trimmer)) :
    insertedRecord left right primary trimmer target trimmer = target ∧
      ∀ i, recordLT (left i) (insertedRecord left right primary trimmer target i) ∧
        recordLT (insertedRecord left right primary trimmer target i) (right i) := by
  have heq : insertedRecord left right primary trimmer target trimmer = target := by
    apply Prod.ext
    · exact htarget
    · simp [insertedRecord]
  refine ⟨heq, ?_⟩
  intro i
  by_cases hi : i = trimmer
  · subst i
    rw [heq]
    exact ⟨hltarget, hrtarget⟩
  · simpa only [insertedRecord, ite_eq_right hi] using
      intermediateLabel_spec (left i) (right i) (primary i) (horder i) (hbetween i).1 (hbetween i).2

/-- Nonnegative physical measures make their cumulative prefix costs monotone. -/
theorem prefixCost_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Monotone (prefixCost μ a) := by
  intro x y hxy
  exact measureReal_mono (Icc_subset_Icc_right hxy)

/-- Strict primary brackets constrain every legal root, not only an extremal one. -/
theorem every_root_in_strict_bracket (F : ℝ → ℝ) (hmono : Monotone F)
    {left right target x : ℝ} (hl : F left < target) (hr : target < F right)
    (hx : F x = target) : left < x ∧ x < right := by
  constructor
  · by_contra h
    have hcost := hmono (le_of_not_gt h)
    rw [hx] at hcost
    exact (not_le_of_gt hl) hcost
  · by_contra h
    have hcost := hmono (le_of_not_gt h)
    rw [hx] at hcost
    exact (not_le_of_gt hr) hcost

/-- A genuinely new formal trim is implemented by one ordinary interval Cut.
The target is an original nonnegative-measure interval cost, and every legal
reply realizes the old global prefix target inside the two physical neighbors. -/
theorem record_insertion_ordinary_cut {Agent : Type*} (cost : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (O : Query Agent → Option ℝ) (hO : IsLegalOracle (measureProfile cost) O)
    (i : Agent) {left right target : ℝ}
    (hl0 : 0 ≤ left) (hlr : left ≤ right) (hr1 : right ≤ 1)
    (hl : prefixCost (cost i) 0 left < target)
    (hr : target < prefixCost (cost i) 0 right) :
    ∃ x, O (.cut i left right (target - prefixCost (cost i) 0 left)) = some x ∧
      left < x ∧ x < right ∧ prefixCost (cost i) 0 x = target := by
  have hnonneg : 0 ≤ prefixCost (cost i) 0 right - prefixCost (cost i) 0 left := by linarith
  have hlegal : Legal (measureProfile cost)
      (.cut i left right (target - prefixCost (cost i) 0 left)) := by
    refine ⟨hl0, hlr, hr1, ?_⟩
    change min 0 (prefixCost (cost i) 0 right - prefixCost (cost i) 0 left) ≤ _ ∧
      _ ≤ max 0 (prefixCost (cost i) 0 right - prefixCost (cost i) 0 left)
    rw [min_eq_left hnonneg, max_eq_right hnonneg]
    constructor <;> linarith
  obtain ⟨x, hx⟩ := hO.complete _ hlegal
  have hreply := (hO.sound _ _ hx).2
  have heq : prefixCost (cost i) 0 x = target := by
    have h := hreply.2
    change prefixCost (cost i) 0 x = prefixCost (cost i) 0 left +
      (target - prefixCost (cost i) 0 left) at h
    linarith
  have hbracket := every_root_in_strict_bracket (prefixCost (cost i) 0)
    (prefixCost_monotone (cost i) 0) hl hr heq
  exact ⟨x, hx, hbracket.1, hbracket.2, heq⟩

end EnvyFreeResearch.Full.Chores
