import EnvyFreeResearch.Full.RefinedChoresTerminalCohortBoundary
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortAdmissible

/-! Provenance for the actual terminal affine oracle execution. All query
 coordinates and retained split endpoints are accounted for by its trace. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary Chores.Suffix
open Chores.ComponentRecording Chores.ComponentPayments Chores.SubCoreEntry
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (homitted : ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible
      (original (data.source s)) H r data.protectedLabel)
    (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
include hknown hsound horiginal hsep hr hH hscale hr_eq homitted hzero hone

theorem TerminalGroup.program_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (package : ChoreComposition.Package (Fin n) RootId) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (TerminalGroup.program data normal original r H group hr0 hH0) prior (some (out,package)) trace) :
    RecordedKnown id (Known points trace) out ∧ Scoped points trace := by
  have hc := RefinedChoresTerminalScans.cache_correct
    (TerminalGroup.selectedOriginal data normal original r H group) group.label r H
    (TerminalGroup.components data normal original r H group) cost c (fun s => hsound (data.source (group.roots s)))
  have hcommon := TerminalGroup.common data normal original r H group cost xs index c hsound horiginal R
    hsep hr hH hscale hr_eq homitted
  have ha := TerminalGroup.admissible data normal original r H group cost xs index c hsound horiginal R
    hsep hr hH hscale hr_eq homitted
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some result =>
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    apply affine_recorded_known cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (TerminalGroup.masked data normal original r H group) hc Subtype.val
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label))
      (fun s i => Clearance.gap_nonnegative (hsound (data.source (group.roots s))).choose_spec i group.label)
      (by simpa using Finset.card_pos.mpr ha.1) (by simp [TerminalGroup.Root]) _
      oracle hpolicy points (TerminalGroup.masked_known data normal original r H group points hknown)
      hzero hone prior out first hfirst
    intro s i
    rw [cached_totals_measure cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (TerminalGroup.masked data normal original r H group) hc s i]
    exact sub_nonneg.mpr ((hcommon s).2.2.2.1 i i.property)

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.program_known
