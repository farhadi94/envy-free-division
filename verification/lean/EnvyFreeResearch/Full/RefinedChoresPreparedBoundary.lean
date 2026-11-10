import EnvyFreeResearch.Full.RefinedChoresTerminalRunBoundary
import EnvyFreeResearch.Full.RefinedChoresParameterConditions
import EnvyFreeResearch.Full.ChoresOuterLocalGeometry

/-! Recorded terminal provenance specialized to the actual preprocessing
 records and the physical prefix's retained and complementary caches. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem prepared_finish_known (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : Outer.EntranceChoice n out.originals.length)
    (hs : (Outer.Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (out.originals.get root))
    (hR0 : CacheKnown points out.residue) (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Completion.Allocation n (Fin n)) :
    ∀ entry : PhysicalTerminalEntry out.originals.get (cachedValue out.residue) (scale n),
      entry.state.data.Good out.originals.get cost.measure (cachedValue out.residue) (scale n) →
      Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (out.originals.get root).piece)
        entry.state.data.cache entry.state.privateCache →
      entry.state.data.Omitted out.originals.get c (cachedValue out.residue) (scale n) →
      (∀ root p, CacheKnown points (entry.state.data.cache root p)) →
      (∀ root p, CacheKnown points (entry.state.privateCache root p)) →
      Executes oracle (finishTerminal out.originals.get (cachedValue out.residue) (scale n) out.residue children entry)
        prior result trace →
      AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  rw [Outer.preprocessing_residue_values cost.measure out hclear]
  intro entry good hold homitted hcache hpriv hex
  have hsound : ∀ root, ∃ V, Snapshot.Sound cost.measure V c (out.originals.get root) :=
    fun root => hchain.member_sound _ (List.get_mem _ _)
  have hc := real_conditions hn
  exact finish_terminal_known cost out.originals.get out.originals id c hsound (fun _ => rfl)
    (material out.residue) _ (scale n) hsep hpos hc.2.1 hc.2.2.1 rfl out.residue hclear.final_cache
    hchain.pieces (fun _ _ => rfl)
    (fun root p => (Outer.preprocessing_original_residue_disjoint cost.measure out hchain hclear root p).symm)
    entry good hold homitted (roots n) (by simpa only [Fintype.card_fin] using hJ.le)
    hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 children hchildren points hknown hcache hpriv hR0 hzero hone
    oracle hpolicy prior trace result hex

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.prepared_finish_known
