import EnvyFreeResearch.Full.RefinedChoresPreparedBoundary
import EnvyFreeResearch.Full.RefinedChoresPreparedPrefix

/-! Provenance through the real continuing branch: run the finite physical
 prefix, finish the selected cohort, then attach fixed clearance allocations. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem continue_prepared_known (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : Outer.EntranceChoice n out.originals.length)
    (hs : (Outer.Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hknown : Outer.PreprocessingKnown points out)
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Completion.Allocation n (Fin n))
    (hex : Executes oracle (continuePrepared c children out a) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  obtain ⟨mid,first,rest,hfirst,hrest,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨entry,tr,he,good,hold,hclosed,homitted,hlabel,hq,hc,hcache,hpriv,hscope⟩ :=
    prepared_prefix_correct cost hn U c out a hs points hknown hzero hone oracle hpolicy prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨inner,second,empty,hsecond,hreturn,htrace⟩ := Executes.split_bind _ _ hrest
  cases hreturn
  simp only [List.append_nil] at htrace
  subst rest
  obtain ⟨hinner,hscope₂⟩ := prepared_finish_known cost hn U c out a hs children hchildren
    (Known points first) (fun root => (hknown.originals _ (List.get_mem _ root)).mono subset_union_left)
    (hknown.residue.mono subset_union_left) (Or.inl hzero) (Or.inl hone) oracle hpolicy
    (prior++first) second inner entry good hold homitted hcache hpriv hsecond
  refine ⟨?_,(scoped_append points first second).mpr ⟨hscope,hscope₂⟩⟩
  apply join_known
  · exact (Outer.batch_allocation_known points out.clearance hknown.clearance).mono subset_union_left
  · simpa only [known_append] using hinner

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.continue_prepared_known
