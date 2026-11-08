import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryEntrance
import EnvyFreeResearch.Full.ChoresOuterLocalDriver
import EnvyFreeResearch.Full.ChoresOuterLocalBudgetScale

/-! Terminal provenance with all scale and geometry hypotheses instantiated
from the actual continuing preprocessing result. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Completion Boundary Parameters
variable {n : ℕ} [NeZero n]

theorem prepared_finish_known (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : EntranceChoice n out.originals.length)
    (hs : (Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (entry : TerminalEntrance out.originals.get (cachedValue out.residue) (scale n))
    (hinv : DriverInvariant entry.data entry.privateCache out.originals.get cost.measure c a.pivot
      (cachedValue out.residue) (scale n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hknown : DataKnown points out.originals.get entry.data)
    (hpriv : ∀ root q, CacheKnown points (entry.privateCache root q))
    (hR0 : CacheKnown points out.residue) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle (finishTerminal out.originals.get (cachedValue out.residue) (scale n)
      out.residue children entry) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  have hv := preprocessing_residue_values cost.measure out hclear
  revert entry
  rw [hv]
  intro entry hinv hknown hpriv hex
  have sc := terminal_scale_real hn
  exact finish_terminal_known cost out.originals c a.pivot
    (fun s => hchain.member_sound _ (List.get_mem _ s)) (material out.residue) (scale n)
    hsep hpos (scale_conditions hn).2.1 (scale_conditions hn).2.2 out.residue hclear.final_cache
    hchain.pieces (fun _ _ => rfl)
    (fun s p => (preprocessing_original_residue_disjoint cost.measure out hchain hclear s p).symm)
    entry hinv (roots n) (by omega) sc.1 sc.2.1 sc.2.2.1 children hchildren points hknown hpriv hR0
    hzero hone oracle hpolicy prior trace result hex
end EnvyFreeResearch.Full.Chores.Outer
