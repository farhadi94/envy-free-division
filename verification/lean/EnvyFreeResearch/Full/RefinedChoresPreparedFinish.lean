import EnvyFreeResearch.Full.RefinedChoresTerminalRun
import EnvyFreeResearch.Full.RefinedChoresChildLedger
import EnvyFreeResearch.Full.RefinedChoresParameterConditions
import EnvyFreeResearch.Full.ChoresOuterLocalGeometry

/-! Physical terminal completion on the actual preprocessing domain, with
proper-population child costs charged by the same capacity recurrence. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem prepared_finish_correct (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : Outer.EntranceChoice n out.originals.length)
    (hs : (Outer.Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent)
        ((totalCapacity k).queries+n*(totalCapacity k).cuts) (totalCapacity k).cuts)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∀ entry : PhysicalTerminalEntry out.originals.get (cachedValue out.residue) (scale n),
      entry.state.data.Good out.originals.get cost.measure (cachedValue out.residue) (scale n) →
      Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (out.originals.get root).piece)
        entry.state.data.cache entry.state.privateCache →
      entry.state.data.Omitted out.originals.get c (cachedValue out.residue) (scale n) →
      ∃ result trace, Executes oracle
        (finishTerminal out.originals.get (cachedValue out.residue) (scale n) out.residue children entry)
        prior result trace ∧
        trace.length ≤ ComponentRecording.budget n n+(19*n*2^n+childQueries n) ∧
        virtualCuts trace ≤ ComponentRecording.budget n n+(19*2^n+childCuts n) ∧
        result.Sound cost.measure id (Outer.preprocessingDomain out) := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  rw [Outer.preprocessing_residue_values cost.measure out hclear]
  intro entry good hold homitted
  have hsound : ∀ root, ∃ V, Snapshot.Sound cost.measure V c (out.originals.get root) :=
    fun root => hchain.member_sound _ (List.get_mem _ _)
  have hc := real_conditions hn
  obtain ⟨result,trace,he,hq,hcut,hphysical⟩ := finish_terminal_correct cost out.originals.get
    out.originals id c hsound (fun _ => rfl) (material out.residue) _ (scale n) hsep hpos
    hc.2.1 hc.2.2.1 rfl out.residue hclear.final_cache hchain.pieces (fun _ _ => rfl)
    (fun root p => (Outer.preprocessing_original_residue_disjoint cost.measure out hchain hclear root p).symm)
    entry good hold homitted (roots n) (by simpa only [Fintype.card_fin] using hJ.le)
    hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 children
    (fun k => (totalCapacity k).queries) (fun k => (totalCapacity k).cuts) hchildren
    (19*n*2^n+childQueries n) (19*2^n+childCuts n)
    (fun B hp hproper => atomic_completion_allowance B hp hproper le_rfl le_rfl)
    (fun A hp _ => exhausted_completion_allowance A hp le_rfl le_rfl)
    oracle hpolicy prior
  refine ⟨result,trace,he,hq,hcut,?_⟩
  simpa only [Snapshot.Chain.pieces,Outer.preprocessing_mutable_domain] using hphysical

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.prepared_finish_correct
