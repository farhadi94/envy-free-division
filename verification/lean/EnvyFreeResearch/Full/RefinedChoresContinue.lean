import EnvyFreeResearch.Full.RefinedChoresPreparedPrefix
import EnvyFreeResearch.Full.RefinedChoresPreparedFinish
import EnvyFreeResearch.Full.RefinedChoresLocalLedger

/-! The continuing branch allocates all mutable material and reattaches the
fixed clearance allocations, with the complete local and recursive ledger. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem continue_prepared_correct (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : Outer.EntranceChoice n out.originals.length)
    (hs : (Outer.Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (points : Set ℝ) (hknown : Outer.PreprocessingKnown points out)
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) (totalCapacity k).cuts)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle (continuePrepared c children out a) prior result trace ∧
      snapshots n*Snapshot.queryBudget n+trace.length ≤ (totalCapacity n).queries ∧
      snapshots n*Snapshot.queryBudget n+virtualCuts trace ≤ (totalCapacity n).cuts ∧
      result.Sound cost.measure id U := by
  obtain ⟨entry,tr0,he0,hgood,hpriv,hclosed,homitted,hpivot,hq0,hc0,hcache,hprivate,hscoped⟩ :=
    prepared_prefix_correct cost hn U c out a hs points hknown hzero hone oracle hpolicy prior
  obtain ⟨inner,tr1,he1,hq1,hc1,hs1⟩ :=
    prepared_finish_correct cost hn U c out a hs children hchildren oracle hpolicy (prior++tr0)
      entry hgood hpriv homitted
  have hjoin := Outer.preprocessing_attach_sound cost.measure out hs.2.1 hs.2.2.1 inner hs1
  have hejoin : Executes oracle
      ((finishTerminal out.originals.get (cachedValue out.residue) (scale n) out.residue children entry).bind
        (fun result => .returned ((Outer.batchAllocation out.clearance).join result)))
      (prior++tr0) ((Outer.batchAllocation out.clearance).join inner) tr1 := by
    simpa only [List.append_nil] using he1.bind
      (fun result => .returned ((Outer.batchAllocation out.clearance).join result)) (Executes.returned _ _)
  refine ⟨(Outer.batchAllocation out.clearance).join inner,tr0++tr1,he0.bind _ hejoin,?_,?_,hjoin⟩
  · have hledger := local_query_ledger hn
    rw [List.length_append]
    omega
  · have hledger := local_cut_ledger hn
    have hcut0 : virtualCuts tr0 ≤ selected n*ComponentRecording.budget n n :=
      (show virtualCuts tr0 ≤ tr0.length from List.countP_le_length).trans hq0
    simp only [virtualCuts,List.countP_append] at hc1 hcut0 ⊢
    omega

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.continue_prepared_correct
