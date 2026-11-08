import EnvyFreeResearch.Full.ChoresOuterLocalProgram
import EnvyFreeResearch.Full.ChoresOuterLocalBudget

/-! Actual preprocessing instantiated with the concrete population parameters. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Parameters
variable {n : ℕ} (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem concrete_prepare_correct (hn : 3 ≤ n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) (material cache) cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle
      (prepareProgram c (roots n) (scale n) (length n) (selected n) cache) prior out trace ∧
      trace.length ≤ snapshots n*Snapshot.queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ snapshots n*Snapshot.cutBudget n ∧
      out.Sound cost (material cache) c (scale n) (roots n) (selected n) := by
  have hcount : (selected n-1)*(n-1)<roots n := by unfold roots; omega
  obtain ⟨out,trace,he,hq,hcut,hs⟩ := prepare_program_correct cost (by omega) oracle hpolicy c
    (roots n) (scale n) (scale_conditions hn).1 (length n) (selected n)
    (clearance_length hn) hcount (material cache) cache hc prior
  refine ⟨out,trace,he,?_,?_,hs⟩
  · simpa only [snapshots,tracked,Nat.add_comm] using hq
  · simpa only [snapshots,tracked,Nat.add_comm] using hcut

end EnvyFreeResearch.Full.Chores.Outer
