import EnvyFreeResearch.Full.ChoresOuterLocalDriver
import EnvyFreeResearch.Full.ChoresOuterLocalTerminalCorrect
import EnvyFreeResearch.Full.ChoresOuterLocalBudgetScale

/-! The real terminal completion on the mutable preprocessing domain. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Parameters
variable {n : ℕ} [NeZero n]

theorem prepared_finish_correct (cost : Costs n) (hn : 3 ≤ n)
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
    ∀ entry : TerminalEntrance out.originals.get (cachedValue out.residue) (scale n),
      DriverInvariant entry.data entry.privateCache out.originals.get cost.measure c a.pivot
        (cachedValue out.residue) (scale n) →
      ∃ result trace, Executes oracle
        (finishTerminal out.originals.get (cachedValue out.residue) (scale n) out.residue children entry)
        prior result trace ∧
        trace.length ≤ ComponentRecording.budget n n+19*2^n*n+childQueries n ∧
        virtualCuts trace ≤ SubCore.sourceBudget n+19*2^n+childCuts n ∧
        result.Sound cost.measure id (preprocessingDomain out) := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  rw [preprocessing_residue_values cost.measure out hclear]
  intro entry hinv
  have hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (out.originals.get root) :=
    fun root => hchain.member_sound _ (List.get_mem _ _)
  have hsc := terminal_scale_real hn
  obtain ⟨result,trace,he,hq,hcut,hphysical⟩ := finish_terminal_correct cost out.originals c a.pivot
    hsound (material out.residue) (scale n) hsep hpos (scale_conditions hn).2.1
    (scale_conditions hn).2.2 out.residue hclear.final_cache hchain.pieces (fun _ _ => rfl)
    (fun root p => (preprocessing_original_residue_disjoint cost.measure out hchain hclear root p).symm)
    entry hinv (roots n) (by omega) hsc.1 hsc.2.1 hsc.2.2.1 hsc.2.2.2 children hchildren oracle hpolicy prior
  refine ⟨result,trace,he,hq,hcut,?_⟩
  simpa only [Snapshot.Chain.pieces,preprocessing_mutable_domain] using hphysical

end EnvyFreeResearch.Full.Chores.Outer
