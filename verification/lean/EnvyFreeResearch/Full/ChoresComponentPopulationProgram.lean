import EnvyFreeResearch.Full.ChoresComponentBoundaryAssembly
import EnvyFreeResearch.Full.ChoresComponentPopulationTree

/-! An actual well-founded native-population recursion. The local outer step
is an explicit program parameter whose correctness must still be instantiated
by the concrete scheduler/completion driver. The child wrapper is the proved
original-query program, with additive Q + n*C recording cost. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

structure Costs (n : ℕ) where
  measure : Fin n → Measure ℝ
  finite : ∀ i, IsFiniteMeasure (measure i)
  atomless : ∀ i, NullSingletonClass (measure i)

instance {n : ℕ} (cost : Costs n) (i : Fin n) : IsFiniteMeasure (cost.measure i) := cost.finite i
instance {n : ℕ} (cost : Costs n) (i : Fin n) : NullSingletonClass (cost.measure i) := cost.atomless i

def Costs.pullback {n k : ℕ} (cost : Costs n) (agent : Fin k → Fin n) : Costs k :=
  ⟨fun i => cost.measure (agent i), fun _ => inferInstance, fun _ => inferInstance⟩

/-- A complete local-domain protocol contract, including actual original
queries and a compositional coordinate-provenance conclusion. -/
def Specification {n k : ℕ} (cost : Costs n) (agent : Fin k → Fin n)
    (program : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin k)))
    (Q C : ℕ) : Prop :=
  ∀ cache, CacheValid (measureProfile cost.measure) (material cache) cache →
    ∀ (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ),
      AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle →
      ∀ prior, ∃ out trace, Executes oracle (program cache) prior out trace ∧
        trace.length ≤ Q ∧ virtualCuts trace ≤ C ∧ out.Sound cost.measure agent (material cache) ∧
        Boundary.Scoped {x | Aligned cache x} trace ∧
        Boundary.AllocationKnown (Boundary.Known {x | Aligned cache x} trace) out

def wrap {n k : ℕ} (agent : Fin k → Fin n)
    (native : List (Parent k) → Program (Query (Fin k)) ℝ (Allocation k (Fin k)))
    (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (Allocation n (Fin k)) :=
  (ActivePopulation.program agent cache (native (ActivePopulation.projectCache agent cache))).bind
    (fun out => .returned out.allocation)

theorem wrap_specification {n k : ℕ} (cost : Costs n) (agent : Fin k → Fin n)
    (native : List (Parent k) → Program (Query (Fin k)) ℝ (Allocation k (Fin k)))
    (Q C : ℕ) (hnative : Specification (cost.pullback agent) id native Q C) :
    Specification cost agent (wrap agent native) (Q+n*C) C := by
  intro cache hc oracle hpolicy prior
  have hchild : ∀ childOracle : AdaptiveOracle.Policy (Query (Fin k)) ℝ,
      AdaptiveOracle.IsLegalPolicy (measureProfile (fun i => cost.measure (agent i))) childOracle →
      ∃ out trace, Executes childOracle (native (ActivePopulation.projectCache agent cache)) [] out trace ∧
        trace.length ≤ Q ∧ virtualCuts trace ≤ C ∧
        out.Sound (fun i => cost.measure (agent i)) id (material cache) ∧
        Boundary.Scoped {x | Aligned (ActivePopulation.projectCache agent cache) x} trace ∧
        (∀ x ∈ ActivePopulation.endpoints out,
          x ∈ Boundary.Known {x | Aligned (ActivePopulation.projectCache agent cache) x} trace) := by
    intro childOracle hchildPolicy
    have hproject := ActivePopulation.project_cache_valid (measureProfile cost.measure) agent
      (material cache) cache hc
    have hproject' : CacheValid (measureProfile (cost.pullback agent).measure)
        (material (ActivePopulation.projectCache agent cache)) (ActivePopulation.projectCache agent cache) := by
      simpa only [ActivePopulation.project_material, Costs.pullback, ActiveCore.profile, measureProfile] using hproject
    obtain ⟨out, trace, hexec, hQ, hC, hs, hscope, hpoints⟩ :=
      hnative (ActivePopulation.projectCache agent cache) hproject' childOracle hchildPolicy []
    exact ⟨out, trace, hexec, hQ, hC,
      by simpa only [ActivePopulation.project_material, Costs.pullback] using hs,
      hscope, ActivePopulation.endpoints_known _ out hpoints⟩
  obtain ⟨out, trace, hexec, hQ, hC, hs, _, _, _, hscope, hpoints⟩ :=
    ActivePopulation.program_correct cost.measure agent (material cache) cache hc
      (native (ActivePopulation.projectCache agent cache)) Q C hchild oracle hpolicy prior
  refine ⟨out.allocation, trace, ?_, hQ, hC, hs, hscope, ?_⟩
  · simpa only [wrap, List.append_nil] using hexec.bind
      (fun out => Program.returned out.allocation) (Executes.returned _ _)
  · intro i p hp
    have he := ActivePopulation.mem_endpoints out.allocation i p hp
    exact ⟨hpoints p.left he.1, hpoints p.right he.2⟩

abbrev ChildPrograms (n : ℕ) :=
  ∀ k, 0 < k → k < n → (Fin k ↪ Fin n) →
    List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin k))

abbrev Step := ∀ n, ChildPrograms n →
  List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n))

/-- Every recursive call is on an actually smaller population, with its
native cache projected from the current original-observer cache. -/
def recursiveProgram (step : Step) (n : ℕ) :
    List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin n)) :=
  Nat.strongRecOn n (fun m recurse =>
    step m (fun k _ hsmaller agent => wrap agent (recurse k hsmaller)))

theorem recursive_equation (step : Step) (n : ℕ) :
    recursiveProgram step n =
      step n (fun k _ _hsmaller agent => wrap agent (recursiveProgram step k)) := by
  exact Nat.strongRecOn_eq _ n

/-- Closing the local outer-step obligation closes all recursion. This is an
induction kernel only: the actual scheduler must supply `hstep`, and the
actual separate query/Cut recurrence must supply Q and C. -/
theorem recursive_specification (step : Step) (Q C : ℕ → ℕ)
    (hstep : ∀ n, 0 < n → ∀ cost : Costs n, ∀ children : ChildPrograms n,
      (∀ k hkpos hklt (agent : Fin k ↪ Fin n),
        Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k)) →
      Specification cost id (step n children) (Q n) (C n)) :
    ∀ n, 0 < n → ∀ cost : Costs n,
      Specification cost id (recursiveProgram step n) (Q n) (C n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn cost
    rw [recursive_equation]
    apply hstep n hn cost
    intro k hkpos hklt agent
    exact wrap_specification cost agent (recursiveProgram step k) (Q k) (C k)
      (ih k hklt hkpos (cost.pullback agent))

end EnvyFreeResearch.Full.Chores.Population
