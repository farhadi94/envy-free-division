import EnvyFreeResearch.Full.ChoresUnionCore

/-! Recording all returned Core endpoints. This final pass costs at most
3n² ordinary Evals and no Cuts, and makes every allocated prefix and
residual suffix a union of complete cached components. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ}

def alignManyProgram : List ℝ → List (Parent n) → Program (Query (Fin n)) ℝ (List (Parent n))
  | [], cache => .returned cache
  | x::xs, cache => (alignProgram x cache).bind (alignManyProgram xs)

theorem align_many_correct (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (U : Set ℝ) (points : List ℝ) (cache : List (Parent n)) (hc : CacheValid P U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (alignManyProgram points cache) prior fresh trace ∧
      trace.length ≤ n*points.length ∧ virtualCuts trace = 0 ∧ CacheValid P U fresh ∧
      (∀ x ∈ points, Aligned fresh x) ∧ (∀ x, Aligned cache x → Aligned fresh x) ∧
      fresh.length ≤ cache.length+points.length := by
  induction points generalizing cache prior with
  | nil => exact ⟨cache,[],Executes.returned _ _,by simp,by simp [virtualCuts],hc,
      by simp,fun _ h => h,by simp⟩
  | cons x xs ih =>
    obtain ⟨first,t₁,hexec₁,hlen₁,hcuts₁,hcache₁,halign₁,hold₁,hcount₁⟩ :=
      align_program_cache P oracle hpolicy U x cache hc prior
    obtain ⟨fresh,t₂,hexec₂,hlen₂,hcuts₂,hcache₂,halign₂,hold₂,hcount₂⟩ :=
      ih first hcache₁ (prior++t₁)
    refine ⟨fresh,t₁++t₂,hexec₁.bind _ hexec₂,?_,?_,hcache₂,?_,
      fun y hy => hold₂ y (hold₁ y hy),?_⟩
    · rw [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · change (t₁++t₂).countP (fun qr => isCutQuery qr.1) = 0
      rw [List.countP_append,hcuts₁]
      simpa only [virtualCuts,zero_add] using hcuts₂
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hold₂ _ halign₁
      · exact halign₂ y hy
    · simp only [List.length_cons]
      omega

def coreEndpoints : IntervalCore.Outcome n → List ℝ
  | .zero _ => []
  | .prefixes parent s =>
      List.ofFn (fun p => (parent p).left) ++
      (List.ofFn (fun p => (s.endpoint p).point) ++ List.ofFn (fun p => (parent p).right))

theorem core_endpoint_count (out : IntervalCore.Outcome n) : (coreEndpoints out).length ≤ 3*n := by
  cases out <;> simp [coreEndpoints] <;> omega

def CoreAligned (cache : List (Parent n)) : IntervalCore.Outcome n → Prop
  | .zero _ => True
  | .prefixes parent s => ∀ p, Aligned cache (parent p).left ∧
      Aligned cache (s.endpoint p).point ∧ Aligned cache (parent p).right

theorem core_aligned_of_endpoints (cache : List (Parent n)) (out : IntervalCore.Outcome n)
    (h : ∀ x ∈ coreEndpoints out, Aligned cache x) : CoreAligned cache out := by
  cases out with
  | zero z => trivial
  | prefixes parent s =>
    intro p
    refine ⟨h _ ?_,h _ ?_,h _ ?_⟩ <;> simp [coreEndpoints]

def cachedDomainCoreProgram (c : Fin n) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (IntervalCore.Outcome n × List (Parent n)) :=
  (domainCoreProgram c cache).bind (fun pair =>
    (alignManyProgram (coreEndpoints pair.1) pair.2).bind (fun fresh => .returned (pair.1,fresh)))

def cachedDomainCoreBudget (n : ℕ) : ℕ := domainCoreBudget n+3*n^2

/-- Core with a fully refined output-domain cache. The additional endpoint
recording is explicit and charged; no endpoint-provenance assumption is
needed about the virtual Core. -/
theorem cached_domain_core_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome n, ∃ fresh : List (Parent n),
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (cachedDomainCoreProgram c cache) prior (out,fresh) trace ∧
      trace.length ≤ cachedDomainCoreBudget n ∧
      virtualCuts trace ≤ n-1+IntervalCore.trimBudget n ∧
      DomainCorrect cost U c out ∧ IntervalCore.Cached (restrictedProfile cost U) out ∧
      CacheValid (measureProfile cost) U fresh ∧ CoreAligned fresh out := by
  obtain ⟨out,first,t₁,hexec₁,hlen₁,hcuts₁,hcorrect,hcached,hfirst⟩ :=
    domain_core_correct hn cost oracle hpolicy U cache hc c prior
  obtain ⟨fresh,t₂,hexec₂,hlen₂,hcuts₂,hfresh,halign,hold,hcount⟩ :=
    align_many_correct (measureProfile cost) oracle hpolicy U (coreEndpoints out) first hfirst (prior++t₁)
  have htail : Executes oracle
      ((alignManyProgram (coreEndpoints out) first).bind (fun fresh => Program.returned (out,fresh)))
      (prior++t₁) (out,fresh) t₂ := by
    simpa only [List.append_nil] using hexec₂.bind (fun fresh => Program.returned (out,fresh))
      (Executes.returned _ _)
  refine ⟨out,fresh,t₁++t₂,hexec₁.bind _ htail,?_,?_,hcorrect,hcached,hfresh,
    core_aligned_of_endpoints fresh out halign⟩
  · rw [List.length_append]
    calc
      t₁.length+t₂.length ≤ domainCoreBudget n+n*(coreEndpoints out).length :=
        Nat.add_le_add hlen₁ hlen₂
      _ ≤ domainCoreBudget n+n*(3*n) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left n (core_endpoint_count out)) _
      _ = cachedDomainCoreBudget n := by unfold cachedDomainCoreBudget; ring
  · change (t₁++t₂).countP (fun qr => isCutQuery qr.1) ≤ _
    rw [List.countP_append]
    change virtualCuts t₁+virtualCuts t₂ ≤ _
    simpa only [hcuts₂,add_zero] using hcuts₁

end EnvyFreeResearch.Full.Chores.OrderedUnion
