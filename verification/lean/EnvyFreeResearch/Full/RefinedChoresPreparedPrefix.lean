import EnvyFreeResearch.Full.RefinedChoresPhysicalEntrance
import EnvyFreeResearch.Full.RefinedChoresParameterConditions
import EnvyFreeResearch.Full.ChoresOuterLocalGeometry
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryPreprocessing

/-! Actual preprocessing records initialize the root-local physical prefix.
All retained/private endpoints remain in the original query ledger. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.Boundary
open RefinedChoresParameters RefinedChoresData
variable {n : ℕ} [NeZero n]

theorem prepared_prefix_correct (cost : Costs n) (hn : 3 ≤ n)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : Outer.EntranceChoice n out.originals.length)
    (hs : (Outer.Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (points : Set ℝ) (hknown : Outer.PreprocessingKnown points out)
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ entry : PhysicalTerminalEntry out.originals.get (cachedValue out.residue) (scale n),
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (entranceProgram a out.originals.get (cachedValue out.residue) (scale n))
        prior (some entry) trace ∧
      entry.state.data.Good out.originals.get cost.measure (cachedValue out.residue) (scale n) ∧
      Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (out.originals.get root).piece)
        entry.state.data.cache entry.state.privateCache ∧
      entry.state.data.closed=(entranceData a out.originals.get).closed ∧
      entry.state.data.Omitted out.originals.get c (cachedValue out.residue) (scale n) ∧
      entry.state.data.protectedLabel=a.pivot ∧
      trace.length ≤ selected n*ComponentRecording.budget n n ∧
      virtualCuts trace ≤ selected n*SubCore.sourceBudget n ∧
      (∀ root p, CacheKnown (Known points trace) (entry.state.data.cache root p)) ∧
      (∀ root p, CacheKnown (Known points trace) (entry.state.privateCache root p)) ∧
      Scoped points trace := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  have hsound : ∀ root, ∃ V, Snapshot.Sound cost.measure V c (out.originals.get root) :=
    fun root => hchain.member_sound _ (List.get_mem _ _)
  have hc := real_conditions hn
  rw [← Outer.preprocessing_residue_values cost.measure out hclear] at had
  exact entrance_program_correct out.originals.get (cachedValue out.residue) (scale n) cost.measure
    out.originals id c hsound (fun _ => rfl) (material out.residue) hsep hpos hc.2.1 hc.2.2.1
    (Outer.preprocessing_residue_values cost.measure out hclear) a had points
    (fun root => hknown.originals _ (List.get_mem _ _)) hzero hone oracle hpolicy prior

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.prepared_prefix_correct
