import EnvyFreeResearch.Full.RefinedChoresLocalProgram
import EnvyFreeResearch.Full.RefinedChoresBudgets
import EnvyFreeResearch.Full.RefinedChoresParameterConditions

/-! Actual preprocessing instantiated with the concrete population parameters. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.QueryProgram Chores.OrderedUnion RefinedChoresParameters
variable {n : ℕ} (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem concrete_prepare_correct (hn : 3 ≤ n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) (material cache) cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle
      (Outer.prepareProgram c (roots n) (scale n) (length n) (selected n) cache) prior out trace ∧
      trace.length ≤ snapshots n*Snapshot.queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ snapshots n*Snapshot.cutBudget n ∧
      out.Sound cost (material cache) c (scale n) (roots n) (selected n) := by
  have hcount : (selected n-1)*(n-1)<roots n := by unfold roots; omega
  obtain ⟨out,trace,he,hq,hcut,hs⟩ := Outer.prepare_program_correct cost (by omega) oracle hpolicy c
    (roots n) (scale n) (real_conditions hn).1 (length n) (selected n)
    (clearance_length (by omega : 2 ≤ n)) hcount (material cache) cache hc prior
  refine ⟨out,trace,he,?_,?_,hs⟩
  · simpa only [snapshots,Parameters.tracked,Nat.add_comm] using hq
  · simpa only [snapshots,Parameters.tracked,Nat.add_comm] using hcut

end EnvyFreeResearch.Full.RefinedChoresLocal
