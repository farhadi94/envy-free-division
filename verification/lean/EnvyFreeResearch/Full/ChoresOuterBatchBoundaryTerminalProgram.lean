import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryTerminal

/-! The terminal affine boundary contract with its feasibility obligations
derived from the actual classified scan and clearance table. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Equalizers Snapshot Frontier Scheduler ComponentRecording ComponentPayments SubCorePhysical SubCoreEntry Boundary
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

theorem terminal_program_known
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
    (R : Set ℝ) (H : ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (data : Data n RootId) [Nonempty (Fin data.size)]
    (p : Fin n) (t : Reveal.TerminalClass n)
    (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
    (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
      (fun i => (cost i).real R) H (data.pending.partition.component p)
      data.pending.partition.representative=.inl t)
    (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
      ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (xs.get (index root)))
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior trace : History (Query (Fin n)) ℝ)
    (out : ComponentClosed.Result (Root := Fin data.size) t.participants)
    (package : ChoreComposition.Package (Fin n) RootId)
    (h : Executes oracle (Terminal.terminalProgram data (fun root => xs.get (index root))
      (fun i => (cost i).real R) H p t hmany) prior (some (out,package)) trace) :
    RecordedKnown id (Known points trace) out ∧ Scoped points trace := by
  have hcommon (s : Fin data.size) := Terminal.scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative t (hclass s)
    (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p := by
    intro j hj
    exact (data.pending.partition.mem_component p j).mp ((hcommon s).2.1 hj)
  have hc := Terminal.masked_correct data (fun root => xs.get (index root))
    (fun i => (cost i).real R) H cost c hsound
  apply closed_group_known data.pending data.visited t.participants p data.packages data.frames
    (originalGaps data (fun root => xs.get (index root))) hmany cost
    (domains (Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative)
    (Terminal.masked data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
    hc _ ⟨p,(hcommon s).1⟩ _ oracle hpolicy points
    (terminal_masked_known data _ _ H points hknown) hzero hone prior trace out package h
  · intro root q i
    obtain ⟨U,hs⟩ := hsound (data.source root)
    exact Clearance.gap_nonnegative hs i q
  · intro root i
    rw [cached_totals_measure cost _ _ hc root i]
    simp only [ComponentPayments.domains,offsets,hlabel i i.property]
    exact sub_nonneg.mpr ((hcommon root).2.2.2.1 i i.property)
end EnvyFreeResearch.Full.Chores.Outer
