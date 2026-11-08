import EnvyFreeResearch.Full.UpperBaseCasesHalf
import EnvyFreeResearch.Full.UpperBaseCasesChoiceGeometry

/-! Actual two-agent cut-and-choose on an arbitrary recorded residue,
with one Cut, all original observer records, and no additional queries. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperBaseCases
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQueryPrograms
open Chores.QueryProgram
variable {n : ℕ}

def finish (chores : Bool) (cutter chooser : Fin n) (out : (Fin 1 → ℝ) × State n) :=
  choice chores (leftState out.2 (out.1 0)) (rightState out.2 (out.1 0)) cutter chooser

def cutAndChooseProgram (chores : Bool) (origin : State n) (cutter chooser : Fin n) :
    QProgram n (Fin n → State n) :=
  (halfProgram origin cutter).bind (fun out => .returned (finish chores cutter chooser out))

def cutAndChoose (policy : Policy n) (chores : Bool) (origin : State n) (cutter chooser : Fin n) :=
  finish chores cutter chooser (halfRun policy origin cutter)

theorem cutAndChoose_executes (policy : Policy n) (chores : Bool)
    (origin : State n) (cutter chooser : Fin n) :
    ∃ trace, Executes (totalPolicy policy) (cutAndChooseProgram chores origin cutter chooser)
      origin.history (cutAndChoose policy chores origin cutter chooser) trace ∧
      trace.length ≤ n+1 ∧ (trace.map Prod.fst).countP isCut ≤ 1 := by
  obtain ⟨trace,hrun,hh,hq,hc⟩ := half_executes policy origin cutter
  refine ⟨trace,?_,hq,hc⟩
  have h := hrun.bind (fun out => .returned (finish chores cutter chooser out))
    (Executes.returned (cutAndChoose policy chores origin cutter chooser) (origin.history ++ trace))
  simpa only [cutAndChooseProgram,List.append_nil] using h

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter chooser : Fin n)
  (hpos : 0 < (μ cutter).real (domain origin.cells)) (hne : chooser ≠ cutter)
include hpolicy hgood hpos

theorem cutAndChoose_wellFormed (chores : Bool) (j : Fin n) :
    WellFormed μ (cutAndChoose policy chores origin cutter chooser j) := by
  have hg := half_wellFormed μ policy hpolicy origin hgood cutter hpos
  exact choice_wellFormed μ chores _ _
    (prefix_wellFormed μ _ hg _) (suffix_wellFormed μ _ hg _) cutter chooser j

theorem cutAndChoose_pairwise (chores : Bool) :
    Pairwise (fun i j => Disjoint
      (domain (cutAndChoose policy chores origin cutter chooser i).cells)
      (domain (cutAndChoose policy chores origin cutter chooser j).cells)) :=
  choice_pairwise chores _ _ cutter chooser
    (split_disjoint _ _ (half_wellFormed μ policy hpolicy origin hgood cutter hpos).2.1)

include hne in
theorem cutAndChoose_complete (chores : Bool) :
    (⋃ j, domain (cutAndChoose policy chores origin cutter chooser j).cells) = domain origin.cells := by
  rw [cutAndChoose,finish,choice_complete _ _ _ _ _ hne,
    split_complete _ _ (half_wellFormed μ policy hpolicy origin hgood cutter hpos).2.1
      (half_separated policy origin cutter),half_domain]

include hne in
theorem cutAndChoose_EF (chores : Bool) :
    GlobalCompletion.ActiveEF (if chores then .chore else .cake)
      (fun i j => (μ i).real (domain (cutAndChoose policy chores origin cutter chooser j).cells))
      {cutter,chooser} := by
  have hg := half_wellFormed μ policy hpolicy origin hgood cutter hpos
  apply choice_EF μ chores _ _ (prefix_wellFormed μ _ hg _) (suffix_wellFormed μ _ hg _)
    cutter chooser hne
  have hp := half_prefix_mass μ policy hpolicy origin hgood cutter hpos
  have hs := split_mass μ _ hg _ (half_separated policy origin cutter) cutter
  rw [half_domain] at hs
  linarith

end EnvyFreeResearch.Full.UpperBaseCases
