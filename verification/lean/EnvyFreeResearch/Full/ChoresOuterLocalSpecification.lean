import EnvyFreeResearch.Full.ChoresOuterLocalLarge
import EnvyFreeResearch.Full.ChoresOuterLocalBase

/-! Assembly of the physical local specification with coordinate provenance. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Parameters
variable {n : ℕ} [NeZero n]

theorem large_program_complete_of_coordinates (cost : Costs n) (hn : 3 ≤ n)
    (c : Fin n) (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) ((totalCapacity k).cuts))
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

end EnvyFreeResearch.Full.Chores.Outer
