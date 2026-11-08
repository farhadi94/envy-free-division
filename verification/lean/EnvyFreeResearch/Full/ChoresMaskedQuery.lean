import EnvyFreeResearch.Full.ChoresUnionFullQuery

/-! Ordinary-query execution for parent- and observer-dependent restrictions.
Each logical request selects the queried observer's physical block. Its
answer is obtained by the original oracle, with cached finite-union routing;
no oracle for masked or disconnected valuations is supplied as an input. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Masked
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ} {Root : Type*}

abbrev Cache (Root : Type*) (n : ℕ) := Root → Fin n → List (Parent n)
abbrev TaggedQuery (Root : Type*) (n : ℕ) := Root × Query (Fin n)

def rowProfile (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Fin n → Set ℝ) : Profile (Fin n) :=
  measureProfile (fun i => (cost i).restrict (domains i))

theorem row_legal_iff (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Fin n → Set ℝ) (q : Query (Fin n)) :
    Legal (rowProfile cost domains) q ↔ Legal (restrictedProfile cost (domains q.agent)) q := by
  cases q <;> simp only [Legal,rowProfile,restrictedProfile,Query.agent,measureProfile]

theorem row_reply_iff (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Fin n → Set ℝ) (q : Query (Fin n)) (r : ℝ) :
    ValidReply (rowProfile cost domains) q r ↔
      ValidReply (restrictedProfile cost (domains q.agent)) q r := by
  cases q <;> simp only [ValidReply,rowProfile,restrictedProfile,Query.agent,measureProfile]

theorem row_reply_spec (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Fin n → Set ℝ) (q : Query (Fin n)) (reply : Option ℝ)
    (h : ReplySpec (restrictedProfile cost (domains q.agent)) q reply) :
    ReplySpec (rowProfile cost domains) q reply :=
  ⟨by rw [row_legal_iff]; exact h.1,
    fun r hr => (row_reply_iff cost domains q r).mpr (h.2 r hr)⟩

def CacheCorrect (P : Profile (Fin n)) (domains : Root → Fin n → Set ℝ)
    (cache : Cache Root n) : Prop := ∀ p i, CacheValid P (domains p i) (cache p i)

structure Result (Root : Type*) (n : ℕ) where
  reply : Option ℝ
  cache : Cache Root n

def updateCache (cache : Cache Root n) (p : Root) (i : Fin n) (next : List (Parent n)) : Cache Root n :=
  Function.update cache p (Function.update (cache p) i next)

def dispatchProgram (cache : Cache Root n) (q : TaggedQuery Root n) :
    Program (Query (Fin n)) ℝ (Result Root n) :=
  (fullQueryProgram (cache q.1 q.2.agent) q.2).bind (fun out =>
    .returned ⟨out.reply, updateCache cache q.1 q.2.agent out.cache⟩)

theorem update_cache_correct (P : Profile (Fin n)) (domains : Root → Fin n → Set ℝ)
    (cache : Cache Root n) (hc : CacheCorrect P domains cache)
    (p : Root) (i : Fin n) (next : List (Parent n)) (hn : CacheValid P (domains p i) next) :
    CacheCorrect P domains (updateCache cache p i next) := by
  intro r j
  by_cases hr : r = p
  · subst r
    by_cases hj : j = i
    · subst j
      simpa only [updateCache, Function.update_self] using hn
    · simpa only [updateCache, Function.update_self, Function.update_of_ne hj] using hc p j
  · simpa only [updateCache, Function.update_of_ne hr] using hc r j

/-- A single tagged logical query uses the original physical oracle. The
mask may vary with both parent and observer. All cache entries stay valid;
the two endpoint alignments and every recorded original cost are charged. -/
theorem dispatch_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (domains : Root → Fin n → Set ℝ) (cache : Cache Root n)
    (hc : CacheCorrect (measureProfile cost) domains cache)
    (q : TaggedQuery Root n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result Root n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (dispatchProgram cache q) prior out trace ∧
      trace.length ≤ n*(2+cutCharge q.2) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q.2 ∧
      ReplySpec (rowProfile cost (domains q.1)) q.2 out.reply ∧
      CacheCorrect (measureProfile cost) domains out.cache := by
  obtain ⟨answer,trace,hexec,hlen,hcuts,hreply,hcache,_hold,_hnew,_hboundaries⟩ :=
    full_query_correct cost oracle hpolicy (domains q.1 q.2.agent)
      (cache q.1 q.2.agent) (hc q.1 q.2.agent) q.2 prior
  let out : Result Root n := ⟨answer.reply, updateCache cache q.1 q.2.agent answer.cache⟩
  refine ⟨out,trace,?_,hlen,hcuts,row_reply_spec cost (domains q.1) q.2 _ hreply,
    update_cache_correct _ domains cache hc q.1 q.2.agent answer.cache hcache⟩
  have h := hexec.bind (fun answer => Program.returned
    (⟨answer.reply, updateCache cache q.1 q.2.agent answer.cache⟩ : Result Root n))
    (Executes.returned _ (prior ++ trace))
  simpa only [dispatchProgram,List.append_nil] using h

end EnvyFreeResearch.Full.Chores.Masked
