import EnvyFreeResearch.Full.ChoresComponentBoundaryUnion

/-! Stateful restricted-domain compilation preserves physical endpoint
provenance. A virtual Cut may return a cached boundary; otherwise its
coordinate is a reply to an actual original Cut in the compiled trace. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ} {A : Type*}

theorem known_reply_subset (points : Set ℝ) (q : Query (Fin n)) (r : ℝ)
    (trace : History (Query (Fin n)) ℝ)
    (hr : isCutQuery q = true → r ∈ Known points trace) :
    Known points [(q, r)] ⊆ Known points trace := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · cases q with
    | eval i a b => simp [cutReplies] at hx
    | cut i a b t =>
      have heq : x = r := by simpa [cutReplies] using hx
      exact heq ▸ hr rfl

theorem translate_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (initial : SemanticState (measureProfile cost) U)
    {program : Program (Query (Fin n)) ℝ A} {history : History (Query (Fin n)) ℝ}
    {result : A} {virtualTrace : History (Query (Fin n)) ℝ}
    (hexec : Executes (virtualPolicy cost oracle hpolicy U initial) program history result virtualTrace)
    (points : Set ℝ)
    (hcache : CacheKnown points (historyState cost oracle hpolicy U initial history).cache)
    (hscope : Scoped points virtualTrace) :
    ∃ physicalTrace : History (Query (Fin n)) ℝ,
      Executes oracle (translate program (historyState cost oracle hpolicy U initial history).cache)
        (historyState cost oracle hpolicy U initial history).history
        (result, (historyState cost oracle hpolicy U initial (history ++ virtualTrace)).cache) physicalTrace ∧
      CacheKnown (Known points physicalTrace)
        (historyState cost oracle hpolicy U initial (history ++ virtualTrace)).cache ∧
      Scoped points physicalTrace ∧ Known points virtualTrace ⊆ Known points physicalTrace := by
  induction hexec generalizing points with
  | returned a history =>
    refine ⟨[], ?_, ?_, trivial, subset_rfl⟩
    · simpa only [OrderedUnion.translate, List.append_nil] using
        (Executes.returned (oracle := oracle)
          (a, (historyState cost oracle hpolicy U initial history).cache)
          (historyState cost oracle hpolicy U initial history).history)
    · simpa only [List.append_nil, known_nil] using hcache
  | ask q k history reply a tail hreply hnext ih =>
    let S := historyState cost oracle hpolicy U initial history
    let step := transition cost oracle hpolicy U S q
    have hstep : StepSpec cost oracle U S q step := transition_spec cost oracle hpolicy U S q
    have hr : step.1.reply = some reply := hreply
    obtain ⟨hstepCache, hstepScope, hstepPoint⟩ := full_query_known oracle points S.cache hcache
      q hscope.1 S.history step.1 step.2 hstep.1
    have hsub := known_reply_subset points q reply step.2 (hstepPoint reply hr)
    have hstate : historyState cost oracle hpolicy U initial (history ++ [(q, reply)]) =
        advanceState cost oracle hpolicy U S q :=
      historyState_append_singleton cost oracle hpolicy U initial history q reply
    have hcache' : CacheKnown (Known points step.2)
        (historyState cost oracle hpolicy U initial (history ++ [(q, reply)])).cache := by
      simpa only [hstate, advanceState, S, step] using hstepCache
    obtain ⟨physicalTail, htail, htailCache, htailScope, htailSub⟩ :=
      ih (Known points step.2) hcache' (hscope.2.mono hsub)
    have htail' : Executes oracle (translate (k reply) step.1.cache) (S.history ++ step.2)
        (a, (historyState cost oracle hpolicy U initial (history ++ ((q, reply) :: tail))).cache)
        physicalTail := by
      simpa only [hstate, advanceState, S, step, List.append_assoc, List.singleton_append] using htail
    refine ⟨step.2 ++ physicalTail, ?_, ?_,
      (scoped_append points step.2 physicalTail).mpr ⟨hstepScope, htailScope⟩, ?_⟩
    · rw [OrderedUnion.translate]
      change Executes oracle ((fullQueryProgram S.cache q).bind (fun out =>
        match out.reply with
        | none => Program.failed
        | some r => translate (k r) out.cache)) S.history _ _
      apply hstep.1.bind
      simpa only [hr] using htail'
    · simpa only [known_append, List.append_assoc, List.singleton_append] using htailCache
    · intro x hx
      have hx' : x ∈ Known (Known points [(q, reply)]) tail := by
        simpa only [← known_append, List.singleton_append] using hx
      have hm := htailSub (known_set_mono hsub tail hx')
      simpa only [known_append] using hm

end EnvyFreeResearch.Full.Chores.Boundary
