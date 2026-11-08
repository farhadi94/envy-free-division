import EnvyFreeResearch.Full.ChoresOuterLocalProgram
import EnvyFreeResearch.Full.ChoresOuterLocalBudget
import EnvyFreeResearch.Full.ChoresComponentPopulationCoordinates

/-! The concrete one- and two-agent branches satisfy the same native
capacity and parametric coordinate specification as the recursive step. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion Population Parameters
variable {n k : ℕ}

theorem complete_spec_mono (cost : Costs n) (agent : Fin k → Fin n)
    (program : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin k)))
    {Q C Q' C' : ℕ} (h : CompleteSpec cost agent program Q C)
    (hQ : Q ≤ Q') (hC : C ≤ C') : CompleteSpec cost agent program Q' C' := by
  refine ⟨?_,h.2⟩
  intro cache hc oracle hp prior
  obtain ⟨out,trace,he,hq,hcut,hs,hscope,hknown⟩ := h.1 cache hc oracle hp prior
  exact ⟨out,trace,he,hq.trans hQ,hcut.trans hC,hs,hscope,hknown⟩

theorem concrete_singleton_complete (cost : Costs 1) (children : ChildPrograms 1) :
    CompleteSpec cost id (concreteStep 1 children) (totalCapacity 1).queries (totalCapacity 1).cuts := by
  exact complete_spec_mono cost id singletonProgram (singleton_complete_specification cost)
    (Nat.zero_le _) (Nat.zero_le _)

theorem concrete_pair_complete (cost : Costs 2) (children : ChildPrograms 2) :
    CompleteSpec cost id (concreteStep 2 children) (totalCapacity 2).queries (totalCapacity 2).cuts := by
  have h := capacity_local nativeLocalQueries nativeLocalCuts (by decide : 0 < 2)
  exact complete_spec_mono cost id twoProgram (two_complete_specification cost)
    (by simpa only [nativeLocalQueries,if_pos (by decide : 2 ≤ 2),totalCapacity] using h.1)
    (by simpa only [nativeLocalCuts,if_pos (by decide : 2 ≤ 2),totalCapacity] using h.2)

end EnvyFreeResearch.Full.Chores.Outer
