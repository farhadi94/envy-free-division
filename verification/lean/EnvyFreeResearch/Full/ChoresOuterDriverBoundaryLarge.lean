import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryContinue

/-! Actual local large-population coordinate specification. Preprocessing,
the finite scheduler, and terminal recursion are joined at their real histories. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Completion Boundary Parameters
variable {n : ℕ} [NeZero n]

theorem large_program_known (cost : Costs n) (hn : 3 ≤ n) (c : Fin n)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent)) :
    CoordinateSpec cost (largeProgram c children) := by
  intro cache hc oracle hpolicy prior result trace hex points hcache hzero hone
  obtain ⟨prepared,first,second,hfirst,hsecond,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨actual,tr,he,_,_,hs⟩ := concrete_prepare_correct cost.measure hn oracle hpolicy c cache hc prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨hprepared,hscope⟩ := prepare_program_known (by omega) cost.measure oracle hpolicy
    (material cache) cache hc points hcache hzero hone c (roots n) (scale n) (length n) (selected n)
    prior first prepared he
  cases prepared with
  | failed => exact False.elim hs
  | complete allocation =>
    cases hsecond
    simpa only [List.append_nil,PreparedKnown] using And.intro hscope hprepared
  | continuing out a =>
    obtain ⟨hresult,hscope₂⟩ := continue_prepared_known cost hn (material cache) c out a hs children hchildren
      (Known points first) hprepared.1 hprepared.2 (Or.inl hzero) (Or.inl hone)
      oracle hpolicy (prior++first) second result hsecond
    exact ⟨(scoped_append points first second).mpr ⟨hscope,hscope₂⟩,
      by simpa only [known_append] using hresult⟩
end EnvyFreeResearch.Full.Chores.Outer
