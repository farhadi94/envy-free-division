import EnvyFreeResearch.Full.RefinedChoresContinueBoundary
import EnvyFreeResearch.Full.RefinedChoresPrepare

/-! The actual large-population program satisfies the recursive coordinate
 contract across preprocessing, the finite prefix, and terminal completion. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem large_program_known (cost : Costs n) (hn : 3 ≤ n) (c : Fin n)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      CoordinateSpec cost (children k hkpos hklt agent)) :
    CoordinateSpec cost (largeProgram c children) := by
  intro cache hc oracle hpolicy prior result trace hex points hcache hzero hone
  obtain ⟨prepared,first,second,hfirst,hsecond,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨actual,tr,he,_,_,hs⟩ := concrete_prepare_correct cost.measure hn oracle hpolicy c cache hc prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨hprepared,hscope⟩ := Outer.prepare_program_known (by omega) cost.measure oracle hpolicy
    (material cache) cache hc points hcache hzero hone c (roots n) (scale n) (length n) (selected n)
    prior first prepared he
  cases prepared with
  | failed => exact False.elim hs
  | complete allocation =>
    cases hsecond
    simpa only [List.append_nil,Outer.PreparedKnown] using And.intro hscope hprepared
  | continuing out a =>
    obtain ⟨hresult,hscope₂⟩ := continue_prepared_known cost hn (material cache) c out a hs children hchildren
      (Known points first) hprepared.1 (Or.inl hzero) (Or.inl hone)
      oracle hpolicy (prior++first) second result hsecond
    exact ⟨(scoped_append points first second).mpr ⟨hscope,hscope₂⟩,
      by simpa only [known_append] using hresult⟩

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.large_program_known
