import EnvyFreeResearch.Full.ChoresUnionAlign

/-! Legality checking of restricted-domain query targets from the exact
component cache. Rejected targets return no virtual reply and make no Cut. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical

variable {n : ℕ}

def Geometry : Query (Fin n) → Prop
  | .eval _ a b => 0 ≤ a ∧ a ≤ b ∧ b ≤ 1
  | .cut _ a b _ => 0 ≤ a ∧ a ≤ b ∧ b ≤ 1

def ValidTarget (ps : List (Parent n)) : Query (Fin n) → Prop
  | .eval _ _ _ => True
  | .cut i a b t => 0 ≤ t ∧ t ≤ cachedValue (window a b ps) i

theorem legal_iff_cached (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (ps : List (Parent n)) (hc : CacheValid (measureProfile cost) U ps)
    (q : Query (Fin n)) (hg : Geometry q) (ha : AlignedQuery ps q) :
    Legal (restrictedProfile cost U) q ↔ ValidTarget ps q := by
  cases q with
  | eval i a b => exact ⟨fun _ => trivial,fun _ => hg⟩
  | cut i a b t =>
    have hv := cached_window_eval cost ps hc.1 hc.2.1 U hc.2.2 hg.1 hg.2.1 ha.1 ha.2 i
    have hn : 0 ≤ cachedValue (window a b ps) i :=
      cachedValue_nonnegative (measureProfile cost) (fun j => prefixCost_monotone (cost j) 0)
        (window_valid _ hc.1) i
    simp only [Legal,ExtremalRoots.LegalTarget,← hv,min_eq_left hn,max_eq_right hn,
      hg.1,hg.2.1,hg.2.2,true_and,ValidTarget]

structure OracleResult (n : ℕ) where
  reply : Option ℝ
  cache : List (Parent n)

def ReplySpec (P : Profile (Fin n)) (q : Query (Fin n)) (reply : Option ℝ) : Prop :=
  (reply = none ↔ ¬ Legal P q) ∧ ∀ r, reply = some r → ValidReply P q r

def AcceptedBoundary (q : Query (Fin n)) (out : OracleResult n) : Prop :=
  ∀ r, out.reply = some r → NewBoundary q ⟨r,out.cache⟩

def checkedQueryProgram (ps : List (Parent n)) (q : Query (Fin n)) :
    Program (Query (Fin n)) ℝ (OracleResult n) :=
  if ValidTarget ps q then
    (queryProgram ps q).bind (fun out => .returned ⟨some out.reply,out.cache⟩)
  else .returned ⟨none,ps⟩

theorem checked_query_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (ps : List (Parent n)) (hc : CacheValid (measureProfile cost) U ps)
    (q : Query (Fin n)) (hg : Geometry q) (ha : AlignedQuery ps q)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : OracleResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (checkedQueryProgram ps q) prior out trace ∧
      trace.length ≤ n*cutCharge q ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q ∧
      ReplySpec (restrictedProfile cost U) q out.reply ∧
      CacheValid (measureProfile cost) U out.cache ∧
      (∀ x, Aligned ps x → Aligned out.cache x) ∧ AcceptedBoundary q out := by
  have hiff := legal_iff_cached cost U ps hc q hg ha
  by_cases ht : ValidTarget ps q
  · have hl : Legal (restrictedProfile cost U) q := hiff.mpr ht
    obtain ⟨out,trace,hexec,hlen,hcuts,hreply,hcache,hold,hnew⟩ :=
      query_program_correct cost oracle hpolicy U ps hc q hl ha prior
    refine ⟨⟨some out.reply,out.cache⟩,trace,?_,hlen,hcuts,?_,hcache,hold,?_⟩
    · simpa only [checkedQueryProgram,ite_eq_left ht,List.append_nil] using hexec.bind
        (fun out => Program.returned (⟨some out.reply,out.cache⟩ : OracleResult n))
        (Executes.returned _ _)
    · refine ⟨by simp [hl],?_⟩
      intro r hr
      have he : out.reply = r := Option.some.inj hr
      simpa only [← he] using hreply
    · intro r hr
      have he : out.reply = r := Option.some.inj hr
      simpa only [← he] using hnew
  · have hl : ¬ Legal (restrictedProfile cost U) q := fun h => ht (hiff.mp h)
    refine ⟨⟨none,ps⟩,[],?_,Nat.zero_le _,Nat.zero_le _,?_,hc,fun _ h => h,?_⟩
    · simpa only [checkedQueryProgram,ite_eq_right ht] using
        (Executes.returned (oracle := oracle) (⟨none,ps⟩ : OracleResult n) prior)
    · refine ⟨by simp [hl],?_⟩
      intro r h
      cases h
    · intro r h
      cases h

end EnvyFreeResearch.Full.Chores.OrderedUnion
