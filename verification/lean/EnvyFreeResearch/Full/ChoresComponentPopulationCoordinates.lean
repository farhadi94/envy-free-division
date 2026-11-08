import EnvyFreeResearch.Full.ChoresComponentPopulationBase

/-! Strong population recursion preserves a parametric set of coordinates.
This avoids treating arbitrary gaps in a restricted child domain as free new
boundaries of its parent's cache. The native-to-ambient wrapper preserves this
stronger contract while retaining its Q_child + n*C_child budget. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n k : ℕ} {A : Type*}

def CoordinateSpec (cost : Costs n)
    (program : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin k))) : Prop :=
  ∀ cache, CacheValid (measureProfile cost.measure) (material cache) cache →
    ∀ oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ,
      AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle →
      ∀ prior out trace, Executes oracle (program cache) prior out trace →
        ∀ points, Boundary.CacheKnown points cache → 0 ∈ points → 1 ∈ points →
          Boundary.Scoped points trace ∧ Boundary.AllocationKnown (Boundary.Known points trace) out

def CompleteSpec (cost : Costs n) (agent : Fin k → Fin n)
    (program : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin k))) (Q C : ℕ) : Prop :=
  Specification cost agent program Q C ∧ CoordinateSpec cost program

theorem project_cache_known (agent : Fin k → Fin n) (points : Set ℝ)
    (cache : List (Parent n)) (h : Boundary.CacheKnown points cache) :
    Boundary.CacheKnown points (ActivePopulation.projectCache agent cache) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

theorem unlift_executes (agent : Fin k → Fin n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (prior : History (Query (Fin n)) ℝ)
    (program : Program (Query (Fin k)) ℝ A) (history : History (Query (Fin k)) ℝ)
    (out : A) (lifted : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ActiveCore.liftProgram agent program)
      (prior++ActiveCore.liftHistory agent history) out lifted) :
    ∃ trace, lifted = ActiveCore.liftHistory agent trace ∧
      Executes (ActiveCore.localPolicy agent oracle prior) program history out trace := by
  induction program generalizing history out lifted with
  | returned a => cases h; exact ⟨[], rfl, Executes.returned _ _⟩
  | failed => cases h
  | ask q next ih =>
    cases h with
    | ask q' k prior' reply result tail hreply hnext =>
      have ht : Executes oracle (ActiveCore.liftProgram agent (next reply))
          (prior++ActiveCore.liftHistory agent (history++[(q,reply)])) out tail := by
        simpa only [ActiveCore.liftHistory, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hnext
      obtain ⟨trace, heq, he⟩ := ih reply (history++[(q,reply)]) out tail ht
      refine ⟨(q,reply)::trace, ?_, Executes.ask q next history reply out trace hreply he⟩
      simpa only [ActiveCore.liftHistory, List.map_cons] using
        congrArg (List.cons (ActiveCore.query agent q,reply)) heq

theorem wrap_coordinates (cost : Costs n) (agent : Fin k → Fin n)
    (native : List (Parent k) → Program (Query (Fin k)) ℝ (Allocation k (Fin k)))
    (hnative : CoordinateSpec (cost.pullback agent) native) : CoordinateSpec cost (wrap agent native) := by
  intro cache hc oracle hpolicy prior out trace h points hcache hzero hone
  obtain ⟨recorded, whole, empty, hprogram, hreturn, ht⟩ := Executes.split_bind _ _ h
  cases hreturn
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨child, first, second, hfirst, hsecond, ht⟩ := Executes.split_bind _ _ hprogram
  obtain ⟨fresh, tail, empty, hrecord, hreturn, ht₂⟩ := Executes.split_bind _ _ hsecond
  cases hreturn
  simp only [List.append_nil] at ht₂
  subst second
  subst whole
  obtain ⟨source, hsourceEq, hsource⟩ := unlift_executes agent oracle prior
    (native (ActivePopulation.projectCache agent cache)) [] child first
    (by simpa only [ActiveCore.liftHistory, List.map_nil, List.append_nil] using hfirst)
  have hchildPolicy : AdaptiveOracle.IsLegalPolicy (measureProfile (cost.pullback agent).measure)
      (ActiveCore.localPolicy agent oracle prior) := by
    simpa only [Costs.pullback, ActiveCore.profile, measureProfile] using
      ActiveCore.local_policy_legal (measureProfile cost.measure) agent oracle hpolicy prior
  have hproject : CacheValid (measureProfile (cost.pullback agent).measure)
      (material (ActivePopulation.projectCache agent cache)) (ActivePopulation.projectCache agent cache) := by
    simpa only [ActivePopulation.project_material, Costs.pullback, ActiveCore.profile, measureProfile] using
      ActivePopulation.project_cache_valid (measureProfile cost.measure) agent (material cache) cache hc
  obtain ⟨hsourceScope, hsourcePoints⟩ := hnative (ActivePopulation.projectCache agent cache) hproject
    (ActiveCore.localPolicy agent oracle prior) hchildPolicy [] child source hsource points
    (project_cache_known agent points cache hcache) hzero hone
  have hfirstScope : Boundary.Scoped points first := hsourceEq ▸ ActivePopulation.scoped_lift agent points source hsourceScope
  have hchildPoints : ∀ x ∈ ActivePopulation.endpoints child, x ∈ Boundary.Known points first := by
    rw [hsourceEq, ActivePopulation.known_lift]
    exact ActivePopulation.endpoints_known _ child hsourcePoints
  obtain ⟨hfresh, htail⟩ := Boundary.align_many_known oracle (Boundary.Known points first)
    (Boundary.freshPoints cache (ActivePopulation.endpoints child)).toList
    (fun x hx => hchildPoints x ((Boundary.mem_freshPoints cache (ActivePopulation.endpoints child) x).mp
      (Finset.mem_toList.mp hx)).1)
    cache (hcache.mono subset_union_left) (prior++first) fresh tail hrecord
  refine ⟨(Boundary.scoped_append points first tail).mpr ⟨hfirstScope, htail⟩, ?_⟩
  exact Boundary.AllocationKnown.mono (out := ActivePopulation.restore fresh child)
    (ActivePopulation.restore_known _ fresh hfresh child) (Boundary.known_mono points first tail)

theorem wrap_complete_specification (cost : Costs n) (agent : Fin k → Fin n)
    (native : List (Parent k) → Program (Query (Fin k)) ℝ (Allocation k (Fin k)))
    (Q C : ℕ) (hnative : CompleteSpec (cost.pullback agent) id native Q C) :
    CompleteSpec cost agent (wrap agent native) (Q+n*C) C :=
  ⟨wrap_specification cost agent native Q C hnative.1, wrap_coordinates cost agent native hnative.2⟩

theorem singleton_coordinates (cost : Costs 1) : CoordinateSpec cost singletonProgram := by
  intro cache hc oracle hpolicy prior out trace h points hcache hzero hone
  cases h
  refine ⟨trivial, ?_⟩
  intro i
  simpa only [Boundary.known_nil, ActiveCore.singletonAllocation] using hcache

theorem two_coordinates (cost : Costs 2) : CoordinateSpec cost twoProgram := by
  intro cache hc oracle hpolicy prior out trace h points hcache hzero hone
  obtain ⟨parts, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨hparts, hscope⟩ := Boundary.split_known oracle points (0 : Fin 2) (cachedValue cache 0/2)
    cache hcache prior parts first hf
  refine ⟨hscope, ?_⟩
  intro i p hp
  have hpre : Boundary.CacheKnown (Boundary.Known points first) parts.prefixParts :=
    fun p hp => hparts p (List.mem_append_left _ hp)
  have hsuf : Boundary.CacheKnown (Boundary.Known points first) parts.suffixParts :=
    fun p hp => hparts p (List.mem_append_right _ hp)
  unfold chooseTwo at hp
  split_ifs at hp
  all_goals
    by_cases hi : i = 0
    · simp only [pairAllocation, ite_eq_left hi] at hp
      first | exact hpre p hp | exact hsuf p hp
    · simp only [pairAllocation, ite_eq_right hi] at hp
      first | exact hpre p hp | exact hsuf p hp

theorem singleton_complete_specification (cost : Costs 1) : CompleteSpec cost id singletonProgram 0 0 :=
  ⟨singleton_specification cost, singleton_coordinates cost⟩

theorem two_complete_specification (cost : Costs 2) : CompleteSpec cost id twoProgram 2 1 :=
  ⟨two_specification cost, two_coordinates cost⟩

/-- The actual local scheduler must instantiate this premise. The induction
kernel preserves both query accounting and the stronger coordinate contract. -/
theorem recursive_complete_specification (step : Step) (Q C : ℕ → ℕ)
    (hstep : ∀ n, 0 < n → ∀ cost : Costs n, ∀ children : ChildPrograms n,
      (∀ k hkpos hklt (agent : Fin k ↪ Fin n),
        CompleteSpec cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k)) →
      CompleteSpec cost id (step n children) (Q n) (C n)) :
    ∀ n, 0 < n → ∀ cost : Costs n, CompleteSpec cost id (recursiveProgram step n) (Q n) (C n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn cost
    rw [recursive_equation]
    apply hstep n hn cost
    intro k hkpos hklt agent
    exact wrap_complete_specification cost agent (recursiveProgram step k) (Q k) (C k)
      (ih k hklt hkpos (cost.pullback agent))

end EnvyFreeResearch.Full.Chores.Population
