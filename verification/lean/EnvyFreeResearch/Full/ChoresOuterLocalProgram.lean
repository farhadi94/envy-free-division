import EnvyFreeResearch.Full.ChoresOuterPreprocessingProgram
import EnvyFreeResearch.Full.ChoresOuterDriverProgram
import EnvyFreeResearch.Full.ChoresTerminalPhysicalProgram
import EnvyFreeResearch.Full.ChoresTerminalExtractionMarked
import EnvyFreeResearch.Full.ChoresTerminalResidue
import EnvyFreeResearch.Full.ChoresComponentPopulationExhausted
import EnvyFreeResearch.Full.ChoresComponentPopulationBase

/-! The concrete local recursive step. All branch tests inspect recorded
finite data; all children operate on proper populations. Impossible failure
branches return an explicit empty allocation and are excluded by correctness. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion Population
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

def emptyAllocation : Completion.Allocation n (Fin n) := ⟨fun _ => []⟩

def finishClass (data : Data n RootId) [Nonempty (Fin data.size)]
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) (p : Fin n)
    (oldPrivate : RootId → Fin n → List (Parent n)) (R0 : List (Parent n))
    (children : ChildPrograms n) :
    (t : Reveal.TerminalClass n) →
    (hmany : Fintype.card t.participants < Fintype.card (Fin data.size)) →
    ComponentClosed.Result (Root := Fin data.size) t.participants →
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n))
  | .inl (A,B), hmany, out =>
    if hB : B.Nonempty ∧ B ≠ Finset.univ then
      let base := Terminal.fullAllocation data original r H p (.inl (A,B)) hmany out
      let privateCache := terminalPrivateCache data original A out oldPrivate
      atomicProgram B hB.1 hB.2 base (ComponentExtraction.extractedCache out)
        (fullResidueCache R0 (removePrivate privateCache (Terminal.extractedSlots data A out))) children
    else .returned emptyAllocation
  | .inr A, hmany, out =>
    if hA : A.Nonempty ∧ A ≠ Finset.univ then
      exhaustedProgram A hA.1 hA.2
        (Terminal.fullAllocation data original r H p (.inr A) hmany out)
        (fullResidueCache R0 (terminalPrivateCache data original A out oldPrivate)) children
    else .returned emptyAllocation

def finishTerminal (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (R0 : List (Parent n)) (children : ChildPrograms n) (entry : TerminalEntrance original r H) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  let data := entry.data.filter entry.roots
  letI : Nonempty (Fin data.size) := Terminal.cohort_nonempty entry.data original entry.label r H
    entry.terminalClass entry.roots entry.choice
  let hmany := Terminal.cohort_more_roots entry.data original entry.label r H
    entry.terminalClass entry.roots entry.choice
  (Terminal.terminalProgram data original r H entry.label entry.terminalClass hmany).bind
    (fun result => match result with
      | none => .returned emptyAllocation
      | some (out,_) => finishClass data original r H entry.label entry.privateCache R0 children
          entry.terminalClass hmany out)

def continuePrepared [NeZero n] (c : Fin n) (children : ChildPrograms n)
    (out : Preprocessing.Output n) (a : EntranceChoice n out.originals.length) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  (driverProgram out.originals.get a.pivot (cachedValue out.residue) (Parameters.scale n)
    (Parameters.exponent n) (a.data out.originals.get) (fun _ _ => [])).bind
    (fun entry => match entry with
      | none => .returned emptyAllocation
      | some entry =>
        (finishTerminal out.originals.get (cachedValue out.residue) (Parameters.scale n)
          out.residue children entry).bind
          (fun result => .returned ((batchAllocation out.clearance).join result)))

def largeProgram [NeZero n] (c : Fin n) (children : ChildPrograms n) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  (prepareProgram c (Parameters.roots n) (Parameters.scale n) (Parameters.length n)
    (Parameters.selected n) cache).bind (fun prepared => match prepared with
      | .complete allocation => .returned allocation
      | .failed => .returned emptyAllocation
      | .continuing out a => continuePrepared c children out a)

def concreteStep : Population.Step
  | 0, _, _ => .returned emptyAllocation
  | 1, _, cache => singletonProgram cache
  | 2, _, cache => twoProgram cache
  | n+3, children, cache => largeProgram (0 : Fin (n+3)) children cache

end EnvyFreeResearch.Full.Chores.Outer
