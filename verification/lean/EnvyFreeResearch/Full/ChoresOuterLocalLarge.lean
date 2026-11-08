import EnvyFreeResearch.Full.ChoresOuterLocalContinue

/-! Every reachable branch of the concrete local program returns a complete
physical envy-free allocation within the native recursive capacity. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Parameters
variable {n : ℕ} [NeZero n]

theorem large_program_correct (cost : Costs n) (hn : 3 ≤ n)
    (c : Fin n) (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) ((totalCapacity k).cuts))
    (cache : List (Parent n)) (hc : CacheValid (measureProfile cost.measure) (material cache) cache)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle (largeProgram c children cache) prior result trace ∧
      trace.length ≤ (totalCapacity n).queries ∧ virtualCuts trace ≤ (totalCapacity n).cuts ∧
      result.Sound cost.measure id (material cache) := by
  obtain ⟨prepared,tr0,he0,hq0,hc0,hs⟩ := concrete_prepare_correct cost.measure hn oracle hpolicy c cache hc prior
  cases prepared with
  | failed => exact hs.elim
  | complete result =>
    refine ⟨result,tr0,?_,hq0.trans (preprocessing_queries_capacity hn),
      hc0.trans (preprocessing_cuts_capacity hn),hs⟩
    have he : Executes oracle (largeProgram c children cache) prior result (tr0++[]) := by
      unfold largeProgram
      apply he0.bind
      exact Executes.returned result (prior++tr0)
    simpa only [List.append_nil] using he
  | continuing out a =>
    obtain ⟨result,tr1,he1,hq1,hc1,hs1⟩ := continue_prepared_correct cost hn (material cache) c out a hs
      children hchildren oracle hpolicy (prior++tr0)
    refine ⟨result,tr0++tr1,he0.bind _ he1,?_,?_,hs1⟩
    · rw [List.length_append]
      omega
    · simp only [virtualCuts,List.countP_append] at hc1 ⊢
      omega

end EnvyFreeResearch.Full.Chores.Outer
