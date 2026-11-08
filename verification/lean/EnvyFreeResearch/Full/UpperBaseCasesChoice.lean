import EnvyFreeResearch.Full.UpperZeroRows

/-! Cached cut-and-choose assignment for two distinct active agents. The
physical halves are supplied by the actual one-Cut construction. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

def chooseLeft (chores : Bool) (left right : State n) (chooser : Fin n) : Prop :=
  if chores then total left chooser ≤ total right chooser
  else total right chooser ≤ total left chooser

def choice (chores : Bool) (left right : State n) (cutter chooser j : Fin n) : State n :=
  if j = cutter then (if chooseLeft chores left right chooser then right else left)
  else if j = chooser then (if chooseLeft chores left right chooser then left else right)
  else empty left.history

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem choice_wellFormed (chores : Bool) (left right : State n)
    (hl : WellFormed μ left) (hr : WellFormed μ right) (cutter chooser j : Fin n) :
    WellFormed μ (choice chores left right cutter chooser j) := by
  unfold choice
  split_ifs <;> first | exact hl | exact hr | exact empty_wellFormed μ _ hl.2.2.1

theorem choice_cutter_value (chores : Bool) (left right : State n) (cutter chooser i : Fin n) :
    (μ i).real (domain (choice chores left right cutter chooser cutter).cells) =
      if chooseLeft chores left right chooser then (μ i).real (domain right.cells)
      else (μ i).real (domain left.cells) := by
  unfold choice
  simp only [ite_true]
  split_ifs <;> rfl

theorem choice_chooser_value (chores : Bool) (left right : State n) (cutter chooser i : Fin n)
    (hne : chooser ≠ cutter) :
    (μ i).real (domain (choice chores left right cutter chooser chooser).cells) =
      if chooseLeft chores left right chooser then (μ i).real (domain left.cells)
      else (μ i).real (domain right.cells) := by
  unfold choice
  simp only [hne,ite_false,ite_true]
  split_ifs <;> rfl

theorem choice_EF (chores : Bool) (left right : State n)
    (hl : WellFormed μ left) (hr : WellFormed μ right) (cutter chooser : Fin n)
    (hne : chooser ≠ cutter)
    (hequal : (μ cutter).real (domain left.cells) = (μ cutter).real (domain right.cells)) :
    GlobalCompletion.ActiveEF (if chores then .chore else .cake)
      (fun i j => (μ i).real (domain (choice chores left right cutter chooser j).cells))
      {cutter,chooser} := by
  intro i hi j hj
  simp only [mem_insert_iff,mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rw [GlobalCompletion.margin_self]
  · cases chores <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,GlobalCompletion.margin,
        choice_cutter_value,choice_chooser_value μ _ _ _ _ _ _ hne] <;>
      split_ifs <;> linarith
  · cases chores <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,GlobalCompletion.margin,
        choice_cutter_value,choice_chooser_value μ _ _ _ _ _ _ hne] <;>
      split_ifs with h
    all_goals
      simp only [chooseLeft,Bool.false_eq_true,ite_false,ite_true,
        total_correct μ left hl,total_correct μ right hr] at h
      linarith
  · rw [GlobalCompletion.margin_self]

end EnvyFreeResearch.Full.UpperBaseCases
