import EnvyFreeResearch.Full.ChoresUnionRefinement

/-! One concrete ordinary-query implementation of a restricted-domain
Eval/Cut, together with its persistent global component-cache update. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

structure QueryResult (n : ℕ) where
  reply : ℝ
  cache : List (Parent n)

def queryProgram {n : ℕ} (ps : List (Parent n)) : Query (Fin n) →
    Program (Query (Fin n)) ℝ (QueryResult n)
  | .eval i a b => .returned ⟨cachedValue (window a b ps) i,ps⟩
  | .cut i a b t => (restrictedCutProgram i a t (window a b ps)).bind (fun out =>
      .returned ⟨out.point,replaceWindow a b ps (out.parts.prefixParts++out.parts.suffixParts)⟩)

def AlignedQuery {n : ℕ} (ps : List (Parent n)) : Query (Fin n) → Prop
  | .eval _ a b => Aligned ps a ∧ Aligned ps b
  | .cut _ a b _ => Aligned ps a ∧ Aligned ps b

def cutCharge {n : ℕ} : Query (Fin n) → ℕ
  | .eval _ _ _ => 0
  | .cut _ _ _ _ => 1

def NewBoundary {n : ℕ} : Query (Fin n) → QueryResult n → Prop
  | .eval _ _ _, _ => True
  | .cut _ _ _ _, out => Aligned out.cache out.reply

def CacheValid {n : ℕ} (P : Profile (Fin n)) (U : Set ℝ) (ps : List (Parent n)) : Prop :=
  Valid P ps ∧ Ordered ps ∧ material ps = U

/-- Eval uses only the existing cache. A Cut uses at most one physical Cut
and `n-1` recording Evals, updates the real cache, and preserves every old
recorded endpoint while installing its own reply as a new boundary. -/
theorem query_program_correct {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (ps : List (Parent n)) (hc : CacheValid (measureProfile cost) U ps)
    (q : Query (Fin n)) (hq : Legal (restrictedProfile cost U) q)
    (halign : AlignedQuery ps q) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : QueryResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (queryProgram ps q) prior out trace ∧
      trace.length ≤ n*cutCharge q ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q ∧
      ValidReply (restrictedProfile cost U) q out.reply ∧
      CacheValid (measureProfile cost) U out.cache ∧
      (∀ x, Aligned ps x → Aligned out.cache x) ∧ NewBoundary q out := by
  obtain ⟨hv,ho,hU⟩ := hc
  cases q with
  | eval i a b =>
    refine ⟨⟨cachedValue (window a b ps) i,ps⟩,[],Executes.returned _ _,by simp [cutCharge],
      by simp [cutCharge],?_,⟨hv,ho,hU⟩,fun _ h => h,trivial⟩
    exact cached_window_eval cost ps hv ho U hU hq.1 hq.2.1 halign.1 halign.2 i
  | cut i a b t =>
    have hw := window_within (measureProfile cost) (a := a) (b := b) hv
    have hwindow := window_valid (measureProfile cost) (a := a) (b := b) hv
    have horder := window_ordered (a := a) (b := b) ho
    have hmaterial : material (window a b ps) = U ∩ Ioc a b := by
      rw [window_material halign.1 halign.2,hU]
    have heval := cached_window_eval cost ps hv ho U hU hq.1 hq.2.1 halign.1 halign.2 i
    have hnonneg : 0 ≤ cachedValue (window a b ps) i :=
      cachedValue_nonnegative (measureProfile cost) (fun j => prefixCost_monotone (cost j) 0) hwindow i
    have ht : 0 ≤ t ∧ t ≤ cachedValue (window a b ps) i := by
      simpa only [ExtremalRoots.LegalTarget,← heval,min_eq_left hnonneg,max_eq_right hnonneg] using hq.2.2.2
    obtain ⟨out,trace,hexec,hlen,hcuts,hreply,hvalues,htarget,hsplit,hpre,hsuf,hordered,hpoint⟩ :=
      restricted_cut_program_correct cost oracle hpolicy U i a b t ⟨hq.1,hq.2.1,hq.2.2.1⟩
        (window a b ps) hwindow horder hw hmaterial ht.1 ht.2 prior
    have hfresh : Valid (measureProfile cost) (out.parts.prefixParts++out.parts.suffixParts) :=
      (valid_append _ _ _).mpr ⟨hpre,hsuf⟩
    have hwithin := prefixSplit_within (measureProfile cost) hsplit hw hfresh
    have hgeometry : material (out.parts.prefixParts++out.parts.suffixParts) =
        material (window a b ps) := by rw [material_append,hsplit.cover]
    have hcache : CacheValid (measureProfile cost) U
        (replaceWindow a b ps (out.parts.prefixParts++out.parts.suffixParts)) :=
      ⟨replaceWindow_valid _ hv hfresh,replaceWindow_ordered hq.2.1 ho hordered hwithin,
        (replaceWindow_material halign.1 halign.2 hgeometry).trans hU⟩
    have hold : ∀ x, Aligned ps x →
        Aligned (replaceWindow a b ps (out.parts.prefixParts++out.parts.suffixParts)) x :=
      (replaceWindow_alignment hq.2.1 hsplit hw horder).2
    refine ⟨⟨out.point,replaceWindow a b ps (out.parts.prefixParts++out.parts.suffixParts)⟩,
      trace,?_,by simpa [cutCharge] using hlen,by simpa [cutCharge] using hcuts,hreply,hcache,hold,?_⟩
    · simpa only [queryProgram,List.append_nil] using hexec.bind
        (fun out => Program.returned
          (⟨out.point,replaceWindow a b ps (out.parts.prefixParts++out.parts.suffixParts)⟩ : QueryResult n))
        (Executes.returned _ _)
    · change Aligned _ out.point
      rw [hpoint]
      exact (replaceWindow_alignment hq.2.1 hsplit hw horder).1

end EnvyFreeResearch.Full.Chores.OrderedUnion
