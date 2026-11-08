import EnvyFreeResearch.Full.ChoresOuterLocalFinish
import EnvyFreeResearch.Full.ChoresOuterLocalBudgetLedger

/-! Physical completion and the full continuation ledger, retaining clearance. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Parameters
variable {n : ℕ} [NeZero n]

theorem continue_prepared_correct (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : EntranceChoice n out.originals.length)
    (hs : (Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) ((totalCapacity k).cuts))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle (continuePrepared c children out a) prior result trace ∧
      snapshots n*Snapshot.queryBudget n+trace.length ≤ (totalCapacity n).queries ∧
      snapshots n*Snapshot.cutBudget n+virtualCuts trace ≤ (totalCapacity n).cuts ∧
      result.Sound cost.measure id U := by
  obtain ⟨entry,tr0,he0,hinv,hpos,hsize,hq0,hc0⟩ :=
    prepared_driver_executes cost hn oracle hpolicy U c out a hs prior
  obtain ⟨inner,tr1,he1,hq1,hc1,hs1⟩ :=
    prepared_finish_correct cost hn U c out a hs children hchildren oracle hpolicy (prior++tr0) entry hinv
  have hjoin := preprocessing_attach_sound cost.measure out hs.2.1 hs.2.2.1 inner hs1
  have hejoin : Executes oracle
      ((finishTerminal out.originals.get (cachedValue out.residue) (scale n) out.residue children entry).bind
        (fun result => .returned ((batchAllocation out.clearance).join result)))
      (prior++tr0) ((batchAllocation out.clearance).join inner) tr1 := by
    simpa only [List.append_nil] using he1.bind
      (fun result => .returned ((batchAllocation out.clearance).join result)) (Executes.returned _ _)
  refine ⟨(batchAllocation out.clearance).join inner,tr0++tr1,?_,?_,?_,hjoin⟩
  · exact he0.bind _ hejoin
  · have hledger := local_query_ledger hn hpos hsize
    have hmul : 19*2^n*n=19*n*2^n := by ac_rfl
    rw [hmul] at hq1
    rw [List.length_append]
    omega
  · have hledger := local_cut_ledger hn hpos hsize
    simp only [virtualCuts,List.countP_append] at hc1 ⊢
    omega

end EnvyFreeResearch.Full.Chores.Outer
