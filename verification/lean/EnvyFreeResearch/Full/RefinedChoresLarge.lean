import EnvyFreeResearch.Full.RefinedChoresContinue
import EnvyFreeResearch.Full.RefinedChoresPrepare

/-! Every reachable branch of the concrete local program yields a complete
physical envy-free allocation within the factorial recursive capacity. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem large_program_correct (cost : Costs n) (hn : 3 ≤ n)
    (c : Fin n) (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) (totalCapacity k).cuts)
    (cache : List (Parent n)) (hc : CacheValid (measureProfile cost.measure) (material cache) cache)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle (largeProgram c children cache) prior result trace ∧
      trace.length ≤ (totalCapacity n).queries ∧ virtualCuts trace ≤ (totalCapacity n).cuts ∧
      result.Sound cost.measure id (material cache) := by
  obtain ⟨prepared,tr0,he0,hq0,hc0,hs⟩ := concrete_prepare_correct cost.measure hn oracle hpolicy c cache hc prior
  have hcut0 : virtualCuts tr0 ≤ snapshots n*Snapshot.queryBudget n :=
    (show virtualCuts tr0 ≤ tr0.length from List.countP_le_length).trans hq0
  cases prepared with
  | failed => exact hs.elim
  | complete result =>
    refine ⟨result,tr0,?_,hq0.trans (preprocessing_capacity hn).1,
      hcut0.trans (preprocessing_capacity hn).2,hs⟩
    have he : Executes oracle (largeProgram c children cache) prior result (tr0++[]) := by
      unfold largeProgram
      apply he0.bind
      exact Executes.returned result (prior++tr0)
    simpa only [List.append_nil] using he
  | continuing out a =>
    have hknown := inherited_cache_known (measureProfile cost.measure) cache hc.1 hc.2.1
    have hzero : (0:ℝ) ∈ {x | Aligned cache x} := by
      intro p hp
      exact Or.inr (((valid_iff_forall _ _).mp hc.1 p hp).1.1)
    have hone : (1:ℝ) ∈ {x | Aligned cache x} := by
      intro p hp
      exact Or.inl (((valid_iff_forall _ _).mp hc.1 p hp).1.2.2)
    have hprepared := Outer.prepare_program_known (by omega : 2 ≤ n) cost.measure oracle hpolicy
      (material cache) cache hc {x | Aligned cache x} hknown hzero hone c (roots n) (scale n)
      (length n) (selected n) prior tr0 (Outer.Prepared.continuing out a) he0
    obtain ⟨result,tr1,he1,hq1,hc1,hs1⟩ := continue_prepared_correct cost hn (material cache) c out a hs
      (Known {x | Aligned cache x} tr0) hprepared.1.1 (Or.inl hzero) (Or.inl hone)
      children hchildren oracle hpolicy (prior++tr0)
    refine ⟨result,tr0++tr1,he0.bind _ he1,?_,?_,hs1⟩
    · rw [List.length_append]
      omega
    · simp only [virtualCuts,List.countP_append] at hc1 hcut0 ⊢
      omega

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.large_program_correct
