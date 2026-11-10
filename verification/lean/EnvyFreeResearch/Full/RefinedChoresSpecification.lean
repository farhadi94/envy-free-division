import EnvyFreeResearch.Full.RefinedChoresLarge
import EnvyFreeResearch.Full.ChoresOuterLocalBase

/-! Base populations and assembly of the complete native protocol contract.
Coordinate provenance remains an explicit obligation for the concrete
recursive branch until the boundary proof is instantiated. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population
open RefinedChoresParameters
variable {n : ℕ} [NeZero n]

theorem concrete_singleton_complete (cost : Costs 1) (children : ChildPrograms 1) :
    CompleteSpec cost id (concreteStep 1 children) (totalCapacity 1).queries (totalCapacity 1).cuts :=
  Outer.complete_spec_mono cost id singletonProgram (singleton_complete_specification cost)
    (Nat.zero_le _) (Nat.zero_le _)

theorem concrete_pair_complete (cost : Costs 2) (children : ChildPrograms 2) :
    CompleteSpec cost id (concreteStep 2 children) (totalCapacity 2).queries (totalCapacity 2).cuts := by
  have h := capacity_local envelope envelope (by decide : 0 < 2)
  have hq : 2 ≤ envelope 2 := by norm_num [envelope,Nat.factorial]
  have hc : 1 ≤ envelope 2 := by omega
  exact Outer.complete_spec_mono cost id twoProgram (two_complete_specification cost)
    (hq.trans h.1) (hc.trans h.2)

theorem large_program_complete_of_coordinates (cost : Costs n) (hn : 3 ≤ n)
    (c : Fin n) (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) (totalCapacity k).cuts)
    (hcoordinates : CoordinateSpec cost (largeProgram c children)) :
    CompleteSpec cost id (largeProgram c children) (totalCapacity n).queries (totalCapacity n).cuts := by
  refine ⟨?_,hcoordinates⟩
  intro cache hc oracle hpolicy prior
  obtain ⟨result,trace,he,hq,hcut,hs⟩ := large_program_correct cost hn c children hchildren cache hc oracle hpolicy prior
  have hknown := Boundary.inherited_cache_known (measureProfile cost.measure) cache hc.1 hc.2.1
  have hzero : (0:ℝ) ∈ {x | Aligned cache x} := by
    intro p hp
    exact Or.inr (((valid_iff_forall _ _).mp hc.1 p hp).1.1)
  have hone : (1:ℝ) ∈ {x | Aligned cache x} := by
    intro p hp
    exact Or.inl (((valid_iff_forall _ _).mp hc.1 p hp).1.2.2)
  have hp := hcoordinates cache hc oracle hpolicy prior result trace he _ hknown hzero hone
  exact ⟨result,trace,he,hq,hcut,hs,hp.1,hp.2⟩

end EnvyFreeResearch.Full.RefinedChoresLocal
