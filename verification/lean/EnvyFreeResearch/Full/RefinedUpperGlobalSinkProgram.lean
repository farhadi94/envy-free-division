import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalSinkSelected
import EnvyFreeResearch.Full.UpperQueryPrograms
import EnvyFreeResearch.Full.ProgramMeasurable

/-! A query-free finite branch test separates proper-sink freezing from the
strongly connected continuation. It operates only on the saved anchor. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Sink
open MeasureTheory RefinedUpperGlobalPhysical GlobalCompletion UpperQueryPrograms
open Chores.QueryProgram ProgramMeasurable
open scoped Classical
variable {n : ℕ}

def sinkAvailable (direction : Direction) (a : Anchor n) : Bool :=
  decide (ProperSink (a.edge direction) a.active (selectedSink direction a))

theorem sinkAvailable_iff (direction : Direction) (a : Anchor n) :
    sinkAvailable direction a = true ↔ ¬ StrongOn (a.edge direction) a.active := by
  simp only [sinkAvailable,decide_eq_true_eq]
  constructor
  · intro hs
    exact proper_sink_not_strong _ _ _ hs (fun _ _ h => h.2.1)
  · intro hn
    exact (selectedSink_correct direction a hn).1

theorem sinkAvailable_measurable (direction : Direction) :
    Measurable (sinkAvailable (n := n) direction) := by
  let test : GraphData n → Bool := fun g =>
    decide (ProperSink (fun i j => g.2 i j = true) g.1 (select g))
  have ht : Measurable test := measurable_of_countable _
  convert ht.comp (anchorGraph_measurable direction) using 1
  funext a
  simp only [test,Function.comp_def,anchorGraph,decide_eq_true_eq,sinkAvailable,selectedSink]
  rfl

def program (direction : Direction) (a : Anchor n) : QProgram n (Anchor n) :=
  .returned (selectedFreeze direction a)

theorem program_executes (policy : AdaptiveOracle.Policy (UpperCircularStage.Query n) ℝ)
    (direction : Direction) (a : Anchor n) (history : UpperCircularStage.History n) :
    Executes policy (program direction a) history (selectedFreeze direction a) [] :=
  Executes.returned _ _

theorem program_certified (direction : Direction) : Certified (program (n := n) direction) :=
  Certified.returned _ (selectedFreeze_measurable direction)

theorem no_sink_strong (direction : Direction) (a : Anchor n)
    (h : sinkAvailable direction a = false) : StrongOn (a.edge direction) a.active := by
  by_contra hn
  have ht := (sinkAvailable_iff direction a).mpr hn
  simp [h] at ht

end EnvyFreeResearch.Full.RefinedUpperGlobal.Sink
