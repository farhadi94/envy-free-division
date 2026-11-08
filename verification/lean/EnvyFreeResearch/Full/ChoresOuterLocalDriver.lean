import EnvyFreeResearch.Full.ChoresOuterLocalPrepare
import EnvyFreeResearch.Full.ChoresOuterLocalGeometry
import EnvyFreeResearch.Full.ChoresOuterDriverRun

/-! The actual continuing preprocessing branch starts the complete outer
scheduler using the cached residue values and the selected protected pivot. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Population Parameters
variable {n : ℕ} [NeZero n]

theorem prepared_driver_executes (cost : Costs n) (hn : 3 ≤ n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (U : Set ℝ) (c : Fin n) (out : Preprocessing.Output n)
    (a : EntranceChoice n out.originals.length)
    (hs : (Prepared.continuing out a).Sound cost.measure U c (scale n) (roots n) (selected n))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ entry : TerminalEntrance out.originals.get (cachedValue out.residue) (scale n),
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (driverProgram out.originals.get a.pivot (cachedValue out.residue) (scale n)
        (exponent n) (a.data out.originals.get) (fun _ _ => [])) prior (some entry) trace ∧
      DriverInvariant entry.data entry.privateCache out.originals.get cost.measure c a.pivot
        (cachedValue out.residue) (scale n) ∧
      0 < entry.data.size ∧ entry.data.size ≤ selected n ∧
      trace.length ≤ (selected n-entry.data.size)*ComponentRecording.budget n n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (selected n-entry.data.size)*SubCore.sourceBudget n := by
  obtain ⟨hJ,hchain,hclear,hsep,hpos,had,hgood⟩ := hs
  rw [preprocessing_residue_values cost.measure out hclear]
  exact actual_outer_executes cost.measure c out.originals out.middle hchain (scale n)
    hsep hpos (scale_conditions hn).2.1 (scale_conditions hn).2.2 a had oracle hpolicy prior

end EnvyFreeResearch.Full.Chores.Outer
