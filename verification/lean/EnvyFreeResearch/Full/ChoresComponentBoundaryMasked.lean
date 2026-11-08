import EnvyFreeResearch.Full.ChoresComponentBoundaryCompiler
import EnvyFreeResearch.Full.ChoresComponentBoundaryTagged

/-! Every parent/observer mask keeps its own actual physical cache. The
dispatcher and the complete stateful compiler preserve one global coordinate
ledger, including cached replies to virtual Cuts and arbitrary root choices. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ} {Root A : Type*}

def MaskedCacheKnown (points : Set ℝ) (cache : Masked.Cache Root n) : Prop :=
  ∀ p i, CacheKnown points (cache p i)

theorem MaskedCacheKnown.mono {old more : Set ℝ} {cache : Masked.Cache Root n}
    (h : MaskedCacheKnown old cache) (hm : old ⊆ more) : MaskedCacheKnown more cache :=
  fun p i => (h p i).mono hm

theorem masked_dispatch_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : Masked.Cache Root n) (hc : MaskedCacheKnown points cache)
    (q : Masked.TaggedQuery Root n) (hq : BoundsIn points q.2)
    (prior : History (Query (Fin n)) ℝ) (out : Masked.Result Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Masked.dispatchProgram cache q) prior out trace) :
    MaskedCacheKnown (Known points trace) out.cache ∧ Scoped points trace ∧
      ∀ r, out.reply = some r → isCutQuery q.2 = true → r ∈ Known points trace := by
  obtain ⟨answer, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨hcache, hscope, hreply⟩ := full_query_known oracle points (cache q.1 q.2.agent)
    (hc q.1 q.2.agent) q.2 hq prior answer first hf
  refine ⟨?_, hscope, hreply⟩
  intro p i
  by_cases hp : p = q.1
  · subst p
    by_cases hi : i = q.2.agent
    · subst i
      simpa only [Masked.updateCache, Function.update_self] using hcache
    · simpa only [Masked.updateCache, Function.update_self, Function.update_of_ne hi] using
        (hc q.1 i).mono (show points ⊆ Known points first from subset_union_left)
  · simpa only [Masked.updateCache, Function.update_of_ne hp] using
      (hc p i).mono (show points ⊆ Known points first from subset_union_left)

theorem masked_translate_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (domains : Root → Fin n → Set ℝ) (initial : Masked.SemanticState (measureProfile cost) domains)
    {program : Program (Masked.TaggedQuery Root n) ℝ A} {history : History (Masked.TaggedQuery Root n) ℝ}
    {result : A} {virtualTrace : History (Masked.TaggedQuery Root n) ℝ}
    (hexec : Executes (Masked.virtualPolicy cost oracle hpolicy domains initial) program history result virtualTrace)
    (points : Set ℝ)
    (hcache : MaskedCacheKnown points (Masked.historyState cost oracle hpolicy domains initial history).cache)
    (hscope : ScopedBy Prod.snd points virtualTrace) :
    ∃ physicalTrace : History (Query (Fin n)) ℝ,
      Executes oracle (Masked.translate program (Masked.historyState cost oracle hpolicy domains initial history).cache)
        (Masked.historyState cost oracle hpolicy domains initial history).history
        (result, (Masked.historyState cost oracle hpolicy domains initial (history++virtualTrace)).cache) physicalTrace ∧
      MaskedCacheKnown (Known points physicalTrace)
        (Masked.historyState cost oracle hpolicy domains initial (history++virtualTrace)).cache ∧
      Scoped points physicalTrace ∧ KnownBy Prod.snd points virtualTrace ⊆ Known points physicalTrace := by
  induction hexec generalizing points with
  | returned a history =>
    refine ⟨[], ?_, ?_, trivial, subset_rfl⟩
    · simpa only [Masked.translate, List.append_nil] using
        (Executes.returned (oracle := oracle)
          (a, (Masked.historyState cost oracle hpolicy domains initial history).cache)
          (Masked.historyState cost oracle hpolicy domains initial history).history)
    · simpa only [List.append_nil, known_nil] using hcache
  | ask q k history reply a tail hreply hnext ih =>
    let S := Masked.historyState cost oracle hpolicy domains initial history
    let step := Masked.transition cost oracle hpolicy domains S q
    have hstep : Masked.StepSpec cost oracle domains S q step :=
      Masked.transition_spec cost oracle hpolicy domains S q
    have hr : step.1.reply = some reply := hreply
    change BoundsIn points q.2 ∧ Scoped (Known points [(q.2,reply)]) (projectTrace Prod.snd tail) at hscope
    obtain ⟨hstepCache, hstepScope, hstepPoint⟩ := masked_dispatch_known oracle points S.cache hcache
      q hscope.1 S.history step.1 step.2 hstep.1
    have hsub := known_reply_subset points q.2 reply step.2 (hstepPoint reply hr)
    have hstate : Masked.historyState cost oracle hpolicy domains initial (history++[(q,reply)]) =
        Masked.advanceState cost oracle hpolicy domains S q :=
      Masked.historyState_append_singleton cost oracle hpolicy domains initial history q reply
    have hcache' : MaskedCacheKnown (Known points step.2)
        (Masked.historyState cost oracle hpolicy domains initial (history++[(q,reply)])).cache := by
      simpa only [hstate, Masked.advanceState, S, step] using hstepCache
    obtain ⟨physicalTail, htail, htailCache, htailScope, htailSub⟩ :=
      ih (Known points step.2) hcache' (hscope.2.mono hsub)
    have htail' : Executes oracle (Masked.translate (k reply) step.1.cache) (S.history++step.2)
        (a, (Masked.historyState cost oracle hpolicy domains initial (history++((q,reply)::tail))).cache)
        physicalTail := by
      simpa only [hstate, Masked.advanceState, S, step, List.append_assoc, List.singleton_append] using htail
    refine ⟨step.2++physicalTail, ?_, ?_,
      (scoped_append points step.2 physicalTail).mpr ⟨hstepScope, htailScope⟩, ?_⟩
    · rw [Masked.translate]
      change Executes oracle ((Masked.dispatchProgram S.cache q).bind (fun out =>
        match out.reply with
        | none => Program.failed
        | some r => Masked.translate (k r) out.cache)) S.history _ _
      apply hstep.1.bind
      simpa only [hr] using htail'
    · simpa only [known_append, List.append_assoc, List.singleton_append] using htailCache
    · intro x hx
      change x ∈ Known points ((q.2,reply)::projectTrace Prod.snd tail) at hx
      have hx' : x ∈ Known (Known points [(q.2,reply)]) (projectTrace Prod.snd tail) := by
        simpa only [← known_append, List.singleton_append] using hx
      have hm := htailSub (known_set_mono hsub (projectTrace Prod.snd tail) hx')
      simpa only [known_append] using hm

end EnvyFreeResearch.Full.Chores.Boundary
