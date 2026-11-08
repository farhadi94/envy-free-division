import EnvyFreeResearch.Full.ChoresMainUnitProgram
import EnvyFreeResearch.Full.ChoresComponentPopulationCoordinates
import EnvyFreeResearch.Full.ChoresComponentBoundaryIntervalScope

/-! The public no-cache entry point starts with exactly the endpoints 0,1.
The native coordinate contract is explicit and must be supplied by the actual
population recursion. Initial paid Eval queries introduce no free boundaries. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Boundary
open scoped Classical
variable {n : ℕ}

theorem unit_initial_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior trace : History (Query (Fin n)) ℝ) (cache : List (Parent n))
    (h : Executes oracle (initialCacheProgram n) prior cache trace) :
    CacheKnown (Known points trace) cache ∧ Scoped points trace := by
  obtain ⟨values,first,empty,hfirst,hreturn,htrace⟩ := Executes.split_bind _ _ h
  cases hreturn
  simp only [List.append_nil] at htrace
  subst trace
  refine ⟨?_,values_scoped oracle points 0 1 hzero hone (allAgents n) prior values first hfirst⟩
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact ⟨Or.inl hzero,Or.inl hone⟩

theorem unit_program_known (cost : Population.Costs n) (owner : Fin n)
    (native : List (Parent n) → Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)))
    (hnative : Population.CoordinateSpec cost native)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (out : UnitEntry.Output n)
    (h : Executes oracle (UnitEntry.program owner native) prior out trace) :
    AllocationKnown (Known ({0,1} : Set ℝ) trace) out.allocation ∧ Scoped ({0,1} : Set ℝ) trace := by
  obtain ⟨cache,t₁,tail,hfirst,htail,htrace⟩ := Executes.split_bind _ _ h
  obtain ⟨allocation,t₂,empty,hsecond,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
  cases hreturn
  simp only [List.append_nil] at htailtrace
  subst tail
  subst trace
  obtain ⟨actual,t,hexec,_,_,hc⟩ := initial_cache_correct (measureProfile cost.measure) oracle hpolicy prior
  have heq := (hexec.deterministic hfirst).1
  subst actual
  obtain ⟨hcache,hscope₁⟩ := unit_initial_known oracle ({0,1} : Set ℝ) (by simp) (by simp) prior t₁ cache hfirst
  obtain ⟨hscope₂,hout⟩ := hnative cache ⟨hc.1,hc.2.1,rfl⟩ oracle hpolicy (prior++t₁) allocation t₂ hsecond
    (Known ({0,1} : Set ℝ) t₁) hcache (Or.inl (by simp)) (Or.inl (by simp))
  refine ⟨?_,(scoped_append ({0,1} : Set ℝ) t₁ t₂).mpr ⟨hscope₁,hscope₂⟩⟩
  simpa only [known_append] using hout
end EnvyFreeResearch.Full.Chores.Outer
