import EnvyFreeResearch.Full.ChoresUnionChecked

/-! A total physical interpreter for one arbitrary restricted-domain query.
Unknown endpoints are recorded first; malformed geometry and unavailable
targets are rejected explicitly. Every call goes to the original oracle. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical

variable {n : ℕ}

def queryLeft : Query (Fin n) → ℝ
  | .eval _ a _ => a
  | .cut _ a _ _ => a

def queryRight : Query (Fin n) → ℝ
  | .eval _ _ b => b
  | .cut _ _ b _ => b

theorem alignedQuery_iff (ps : List (Parent n)) (q : Query (Fin n)) :
    AlignedQuery ps q ↔ Aligned ps (queryLeft q) ∧ Aligned ps (queryRight q) := by
  cases q <;> rfl

theorem geometry_of_legal (P : Profile (Fin n)) (q : Query (Fin n))
    (h : Legal P q) : Geometry q := by
  cases q with
  | eval i a b => exact h
  | cut i a b t => exact ⟨h.1,h.2.1,h.2.2.1⟩

def fullQueryProgram (ps : List (Parent n)) (q : Query (Fin n)) :
    Program (Query (Fin n)) ℝ (OracleResult n) :=
  if Geometry q then
    (alignProgram (queryLeft q) ps).bind (fun first =>
      (alignProgram (queryRight q) first).bind (fun second => checkedQueryProgram second q))
  else .returned ⟨none,ps⟩

/-- One logical Eval costs at most `2n` ordinary Evals; one logical Cut costs
at most `3n` ordinary calls and one Cut. Already recorded boundaries need
no alignment calls. No legality or endpoint-alignment premise is imposed on
the virtual query: both valid replies and rejection are proved. -/
theorem full_query_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (ps : List (Parent n)) (hc : CacheValid (measureProfile cost) U ps)
    (q : Query (Fin n)) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : OracleResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (fullQueryProgram ps q) prior out trace ∧
      trace.length ≤ n*(2+cutCharge q) ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q ∧
      ReplySpec (restrictedProfile cost U) q out.reply ∧
      CacheValid (measureProfile cost) U out.cache ∧
      (∀ x, Aligned ps x → Aligned out.cache x) ∧ AcceptedBoundary q out ∧
      (Geometry q → AlignedQuery out.cache q) := by
  by_cases hg : Geometry q
  · obtain ⟨first,t₁,hfirst,hlen₁,hcuts₁,hcache₁,ha₁,hold₁,hcount₁⟩ :=
      align_program_cache (measureProfile cost) oracle hpolicy U (queryLeft q) ps hc prior
    obtain ⟨second,t₂,hsecond,hlen₂,hcuts₂,hcache₂,hb₂,hold₂,hcount₂⟩ :=
      align_program_cache (measureProfile cost) oracle hpolicy U (queryRight q) first hcache₁ (prior++t₁)
    have ha₂ : AlignedQuery second q :=
      (alignedQuery_iff second q).mpr ⟨hold₂ _ ha₁,hb₂⟩
    obtain ⟨out,t₃,hthird,hlen₃,hcuts₃,hreply,hcache₃,hold₃,hnew⟩ :=
      checked_query_correct cost oracle hpolicy U second hcache₂ q hg ha₂ ((prior++t₁)++t₂)
    have htail : Executes oracle
        ((alignProgram (queryRight q) first).bind (fun second => checkedQueryProgram second q))
        (prior++t₁) out (t₂++t₃) := hsecond.bind _ hthird
    refine ⟨out,t₁++(t₂++t₃),?_,?_,?_,hreply,hcache₃,
      fun x hx => hold₃ x (hold₂ x (hold₁ x hx)),hnew,?_⟩
    · simpa only [fullQueryProgram,ite_eq_left hg] using hfirst.bind
        (fun first => (alignProgram (queryRight q) first).bind
          (fun second => checkedQueryProgram second q)) htail
    · simp only [List.length_append]
      calc
        t₁.length+(t₂.length+t₃.length) ≤ n+(n+n*cutCharge q) :=
          Nat.add_le_add hlen₁ (Nat.add_le_add hlen₂ hlen₃)
        _ = n*(2+cutCharge q) := by ring
    · simpa only [List.countP_append,hcuts₁,hcuts₂,zero_add] using hcuts₃
    · intro _
      exact (alignedQuery_iff out.cache q).mpr ⟨hold₃ _ (hold₂ _ ha₁),hold₃ _ hb₂⟩
  · have hl : ¬ Legal (restrictedProfile cost U) q := fun h => hg (geometry_of_legal _ q h)
    refine ⟨⟨none,ps⟩,[],?_,Nat.zero_le _,Nat.zero_le _,?_,hc,fun _ h => h,?_,?_⟩
    · simpa only [fullQueryProgram,ite_eq_right hg] using
        (Executes.returned (oracle := oracle) (⟨none,ps⟩ : OracleResult n) prior)
    · refine ⟨by simp [hl],?_⟩
      intro r h
      cases h
    · intro r h
      cases h
    · exact fun h => (hg h).elim

end EnvyFreeResearch.Full.Chores.OrderedUnion
