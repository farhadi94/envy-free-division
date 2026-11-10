import EnvyFreeResearch.Full.RefinedChoresPhysicalEntrance
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortFinish
import EnvyFreeResearch.Full.RefinedChoresParameters
import EnvyFreeResearch.Full.ChoresOuterPreprocessingProgram
import EnvyFreeResearch.Full.ChoresComponentPopulationBase

/-! Concrete local recursion using root-local paid proposals. The two physical
query programs are the ordinary prefix and the selected terminal cohort.
The fixed clearance allocations are attached only after all live material has
been allocated. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.QueryProgram
open Chores.OrderedUnion Chores.Population RefinedChoresData
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

def emptyAllocation : Completion.Allocation n (Fin n) := ⟨fun _ => []⟩

def finishTerminal (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (R0 : List (Parent n)) (children : ChildPrograms n) (entry : PhysicalTerminalEntry original r H) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  if hpos : (∀ i, 0 ≤ r i) ∧ 0 < H then
    (TerminalGroup.program entry.state.data entry.normal original r H entry.group hpos.1 hpos.2).bind
      (fun result => match result with
        | none => .returned emptyAllocation
        | some (out,_) => TerminalGroup.finishClass entry.state.data entry.normal original r H
            entry.group hpos.1 hpos.2 out entry.state.privateCache R0 children)
  else .returned emptyAllocation

def continuePrepared [NeZero n] (c : Fin n) (children : ChildPrograms n)
    (out : Preprocessing.Output n) (a : Outer.EntranceChoice n out.originals.length) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  (entranceProgram a out.originals.get (cachedValue out.residue) (RefinedChoresParameters.scale n)).bind
    (fun entry => match entry with
      | none => .returned emptyAllocation
      | some entry =>
        (finishTerminal out.originals.get (cachedValue out.residue) (RefinedChoresParameters.scale n)
          out.residue children entry).bind
          (fun result => .returned ((Outer.batchAllocation out.clearance).join result)))

def largeProgram [NeZero n] (c : Fin n) (children : ChildPrograms n) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  (Outer.prepareProgram c (RefinedChoresParameters.roots n) (RefinedChoresParameters.scale n)
    (RefinedChoresParameters.length n) (RefinedChoresParameters.selected n) cache).bind
    (fun prepared => match prepared with
      | .complete allocation => .returned allocation
      | .failed => .returned emptyAllocation
      | .continuing out a => continuePrepared c children out a)

def concreteStep : Population.Step
  | 0, _, _ => .returned emptyAllocation
  | 1, _, cache => singletonProgram cache
  | 2, _, cache => twoProgram cache
  | n+3, children, cache => largeProgram (0 : Fin (n+3)) children cache

end EnvyFreeResearch.Full.RefinedChoresLocal
