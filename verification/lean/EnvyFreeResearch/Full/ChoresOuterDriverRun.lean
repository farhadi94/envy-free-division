import EnvyFreeResearch.Full.ChoresOuterDriverCorrect
import EnvyFreeResearch.Full.ChoresOuterDriverEntrance

/-! The concrete entrance-to-terminal outer protocol, with initial reserve,
protected label and physical private caches instantiated from preprocessing. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical
variable {n : ℕ} [NeZero n] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U R : Set ℝ} (c : Fin n) (xs : List (Snapshot.Output n)) (cache : List (Parent n))
  (chain : Snapshot.Chain cost c U xs cache)
  (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (a : EntranceChoice n xs.length)
  (ha : a.Admissible xs.get c (fun i => (cost i).real R) H (Parameters.selected n))
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
include chain hsep hr hH hscale ha hpolicy

theorem actual_outer_executes (prior : History (Query (Fin n)) ℝ) :
    ∃ out : TerminalEntrance xs.get (fun i => (cost i).real R) H,
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (driverProgram xs.get a.pivot (fun i => (cost i).real R) H
        (Parameters.exponent n) (a.data xs.get) (fun _ _ => [])) prior (some out) trace ∧
      DriverInvariant out.data out.privateCache xs.get cost c a.pivot (fun i => (cost i).real R) H ∧
      0 < out.data.size ∧ out.data.size ≤ Parameters.selected n ∧
      trace.length ≤ (Parameters.selected n-out.data.size)*ComponentRecording.budget n n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (Parameters.selected n-out.data.size)*SubCore.sourceBudget n := by
  have hs : ∀ s, ∃ domain, Snapshot.Sound cost domain c (xs.get s) :=
    fun s => chain.member_sound _ (List.get_mem _ s)
  have hi : DriverInvariant (a.data xs.get) (fun _ _ => []) xs.get cost c a.pivot
      (fun i => (cost i).real R) H := by
    refine ⟨entrance_good cost c xs cache chain a H (by linarith),
      entrance_pool_floor xs.get a c _ H ha,entrance_protected xs.get a c _ H ha,?_⟩
    exact private_initial (measureProfile cost) xs.get
  obtain ⟨out,trace,hex,hout,hsize,hQ,hC⟩ := driver_executes cost xs c a.pivot hs R H hsep hr hH hscale
    oracle hpolicy (Parameters.exponent n) (a.data xs.get) (fun _ _ => []) hi
    (entrance_driver_fuel xs.get a) prior
  have hentrance := entrance_size cost c xs a H (Parameters.selected n) ha
  rw [hentrance] at hsize hQ hC
  exact ⟨out,trace,hex,hout,pool_floor_positive hout.pool,hsize,hQ,hC⟩

end EnvyFreeResearch.Full.Chores.Outer
