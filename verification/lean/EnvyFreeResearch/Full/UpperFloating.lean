import EnvyFreeResearch.Full.UpperFloatingMeasurable

/-!
# Measurable sparse reserve plans from common payment targets

The initial plan gives fraction `t j` of every cell to recipient `j`, and
assigns the unused fraction to `none`. Floating preserves all normalized
observer moments and leaves at most `k²` split cells.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloating

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def commonPlan (t : Agent → ℝ) : PaymentCoord Agent Cell → ℝ := fun c =>
  match c.2 with
  | none => 1 - ∑ j, t j
  | some j => t j

omit [Fintype Cell] in
theorem commonPlan_box (t : Agent → ℝ) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) :
    ∀ c : PaymentCoord Agent Cell, 0 ≤ commonPlan t c ∧ commonPlan t c ≤ 1 := by
  rintro ⟨e, j⟩
  cases j with
  | none =>
    have hn : 0 ≤ ∑ j, t j := Finset.sum_nonneg (fun j _ => ht j)
    dsimp [commonPlan]
    constructor <;> linarith
  | some j =>
    exact ⟨ht j, (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ j)).trans hsum⟩

omit [Fintype Cell] in
theorem commonPlan_row (t : Agent → ℝ) (e : Cell) : ∑ j, commonPlan t (e, j) = 1 := by
  simp [commonPlan, Fintype.sum_option]

theorem commonPlan_moment (a : Agent → Cell → ℝ) (t : Agent → ℝ)
    (hnormal : ∀ i, ∑ e, a i e = 1) (i j : Agent) :
    (∑ e, a i e * commonPlan t (e, some j)) = t j := by
  simp only [commonPlan]
  rw [← Finset.sum_mul, hnormal, one_mul]

/-- Curried finite payment table in the form consumed by whole-cell Repair. -/
def plan (a : Agent → Cell → ℝ) (t : Agent → ℝ) (e : Cell) (j : Option Agent) : ℝ :=
  select a (commonPlan t) (e, j)

/-- Normalized observer rows give exactly the common target moments after
floating. The final split predicate is the same one used by whole payments. -/
theorem plan_spec (a : Agent → Cell → ℝ) (t : Agent → ℝ)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) :
    (∀ e j, 0 ≤ plan a t e j ∧ plan a t e j ≤ 1) ∧
      (∀ e, ∑ j, plan a t e j = 1) ∧
      (∀ i j, (∑ e, a i e * plan a t e (some j)) = t j) ∧
      Frozen (commonPlan t) (fun c : PaymentCoord Agent Cell => plan a t c.1 c.2) ∧
      (Finset.univ.filter (fun e => ∃ j, 0 < plan a t e j ∧ plan a t e j < 1)).card ≤
        Fintype.card Agent ^ 2 := by
  obtain ⟨hbox, hrow, hmom, hfrozen, hcount⟩ :=
    select_spec a (commonPlan t) (commonPlan_box t ht hsum) (commonPlan_row t)
  refine ⟨fun e j => hbox (e, j), hrow, ?_, hfrozen, ?_⟩
  · intro i j
    exact (hmom i j).trans (commonPlan_moment a t hnormal i j)
  · have heq : Finset.univ.filter (fun e => ∃ j, 0 < plan a t e j ∧ plan a t e j < 1) =
        splitCells (select a (commonPlan t)) := by
      rw [splitCells_eq_filter]
      apply Finset.filter_congr
      intro e _
      rfl
    rw [heq]
    exact hcount

section Measurability

variable {X : Type*} [MeasurableSpace X]

omit [Fintype Cell] in
theorem commonPlan_measurable (t : X → Agent → ℝ)
    (ht : ∀ j, Measurable (fun z => t z j)) (c : PaymentCoord Agent Cell) :
    Measurable (fun z => commonPlan (t z) c) := by
  cases h : c.2 with
  | none =>
    have hs : Measurable (fun z => 1 - ∑ j, t z j) :=
      measurable_const.sub (Finset.measurable_sum Finset.univ (fun j _ => ht j))
    convert hs using 1
    funext z
    simp [commonPlan, h]
  | some j => simpa [commonPlan, h] using ht j

/-- The entire curried plan is Borel in cached row values and targets. -/
theorem plan_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (ht : ∀ j, Measurable (fun z => t z j)) :
    Measurable (fun z => plan (a z) (t z)) := by
  have h := select_measurable a (fun z => commonPlan (t z)) ha (commonPlan_measurable t ht)
  exact Measurable.of_eval (fun e => Measurable.of_eval (fun j => (measurable_pi_apply (e, j)).comp h))

end Measurability

end EnvyFreeResearch.Full.UpperFloating
