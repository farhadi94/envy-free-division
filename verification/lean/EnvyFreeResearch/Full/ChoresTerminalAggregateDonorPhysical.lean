import EnvyFreeResearch.Full.ChoresTerminalAggregateDonor
import EnvyFreeResearch.Full.ChoresTerminalCache

/-! The actual donor's numerical table is the original measure of its
installed complementary prefix, with its immutable original baseline. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
open ChoreComposition ComponentDonors ComponentRecording ComponentPayments
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (p : Fin n) (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)
  (hparts : PartsCorrect cost (domains (blocks data original r H)
    data.pending.partition.representative) Subtype.val out)

include hsound good hlabel hparts

theorem actual_donor_physical_value (j : A) (i : Fin n) :
    (actualDonor data original A out j).cost i p =
      (cost i).real ((original (data.source (out.allocation.assigned j))).piece p \
        material (out.parts j).suffixParts) := by
  have hv := affine_piece_value data.pending data.visited data.frames Subtype.val
    (Outer.originalGaps data original) cost (blocks data original r H)
    (fun s q => (original (data.source s)).piece q)
    (fun s q k => material (Outer.equalizerCache data original s q k))
    (fun s q => by rw [blocks_complement data original r H cost c hsound]; exact sdiff_subset)
    (fun s i q k => Outer.original_equalizer_value cost (hsound (data.source s)).choose_spec
      (data.frames s) (good.original_frame s) i q k)
    (fun s q i => Outer.original_gap cost (hsound (data.source s)).choose_spec
      (data.frames s) (good.original_frame s) q i)
    out hparts j i p
  simpa only [actualDonor,PackageGeometry.proposalPiece,affine,affineProposal,ite_true,
    hlabel j j.property] using hv

omit hlabel hparts in
theorem actual_donor_original_baseline (j : A) (i : Fin n) :
    (actualDonor data original A out j).baseline i=
      Equalizers.baselines (original (data.source (out.allocation.assigned j))).parents i := by
  rw [actual_donor_baseline,(good.original_frame _).baseline]

end EnvyFreeResearch.Full.Chores.Terminal
