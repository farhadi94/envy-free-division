import EnvyFreeResearch.Full.ChoresOuterLocalProgram
import EnvyFreeResearch.Full.ChoresMainUnitProgram

/-! Concrete public deterministic protocol. Correctness of the local step
is proved separately before invoking the population induction kernel. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Main
open OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram Completion

def nativeProgram (n : ℕ) :
    List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n)) :=
  Population.recursiveProgram Outer.concreteStep n

def program (n : ℕ) (hn : 0 < n) : Program (Query (Fin n)) ℝ (UnitEntry.Output n) :=
  UnitEntry.program ⟨0,hn⟩ (nativeProgram n)

theorem native_equation (n : ℕ) :
    nativeProgram n=Outer.concreteStep n
      (fun k _ _ agent => Population.wrap agent (nativeProgram k)) :=
  Population.recursive_equation Outer.concreteStep n

theorem native_one : nativeProgram 1=Population.singletonProgram := by
  rw [native_equation]
  rfl

theorem native_two : nativeProgram 2=Population.twoProgram := by
  rw [native_equation]
  rfl

end EnvyFreeResearch.Full.Chores.Main
