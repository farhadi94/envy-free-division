import EnvyFreeResearch.Full.RefinedChoresSpecification
import EnvyFreeResearch.Full.RefinedChoresLargeBoundary

/-! The concrete local step satisfies both the physical query ledger and
 coordinate provenance, with only strictly smaller recursive contracts. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Chores.Population RefinedChoresParameters

theorem concrete_step_complete (n : ℕ) (hn : 0 < n) (cost : Costs n)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      CompleteSpec cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) (totalCapacity k).cuts) :
    CompleteSpec cost id (concreteStep n children) (totalCapacity n).queries (totalCapacity n).cuts := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · exact concrete_singleton_complete cost children
  rcases n with _ | n
  · exact concrete_pair_complete cost children
  apply large_program_complete_of_coordinates cost (by omega) (0 : Fin (n+3)) children
    (fun k hkpos hklt agent => (hchildren k hkpos hklt agent).1)
  exact large_program_known cost (by omega) (0 : Fin (n+3)) children
    (fun k hkpos hklt agent => (hchildren k hkpos hklt agent).2)

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.concrete_step_complete
