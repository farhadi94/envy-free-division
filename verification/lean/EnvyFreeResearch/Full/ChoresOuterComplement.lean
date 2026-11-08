import EnvyFreeResearch.Full.ChoresOuterOpenGroup

/-! Full private-complement bounds after real donor modifications. A
proposal may discard an old equalizer and reset a whole original piece;
the bound therefore controls the entire resulting complement, not just
newly removed material. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open ChoreComposition ComponentDonors ComponentRecording ComponentPayments
open scoped Classical

variable {n : ℕ} {RootId : Type*}
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Snapshot.Output n}
  (hs : Snapshot.Sound cost U c out) (frame : Frame (Fin n) RootId)
  (hframe : frame.Good) (r : Fin n → ℝ) (H : ℝ) (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
  (C : Fin n → Finset (Fin n)) (z : Fin n → Fin n)
  (hinv : ∀ p, Frontier.Invariant (weight out.equalizers p) (rankOf out.equalizers p) r H
    (eligible (weight out.equalizers p) (rankOf out.equalizers p) r H)
    (C p) (frame.allowed p) (frame.forbidden p) (z p))

include hs hframe hr hH hinv

theorem proposal_complement_small (proposal : ChoreComposition.Proposal (Fin n) RootId)
    (hbefore : proposal.before=frame)
    (howner : ∀ p, p ≠ proposal.label → proposal.owner p ∈ frame.allowed p)
    (removed : Set ℝ) (hsmall : ∀ i, (cost i).real removed ≤ (n : ℝ)*r i/H) (p i : Fin n) :
    (cost i).real (out.piece p \ PackageGeometry.proposalPiece out.piece
      (fun p j => material (out.equalizers (p,j)).parts.prefixParts) proposal removed p) ≤ (n : ℝ)*r i/H := by
  unfold PackageGeometry.proposalPiece
  by_cases hexec : proposal.execute=true
  · rw [ite_eq_left hexec]
    by_cases hp : p=proposal.label
    · rw [ite_eq_left hp]
      have hsub : out.piece p \ (out.piece p \ removed) ⊆ removed := by
        intro x hx
        by_contra hnot
        exact hx.2 ⟨hx.1,hnot⟩
      apply (measureReal_mono (μ := cost i) hsub).trans
      exact hsmall i
    · rw [ite_eq_right hp]
      exact old_complement_small cost hs p r H _ _ _ _ (hinv p) hr hH _ (howner p hp) i
  · rw [ite_eq_right hexec,hbefore]
    exact old_complement_small cost hs p r H _ _ _ _ (hinv p) hr hH _ (hframe.1 p) i

section OpenGroup
variable [Fintype RootId] (data : Data n RootId) [Nonempty (Fin data.size)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (cutter : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U cutter (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hpos : ∀ i, 0 < (cost i).real R) (hHlarge : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : Components.ProposalCycle (data.pending.outgoing hall))
  (result : ComponentBatch.Result data.pending hall cycle)
  (hparts : PartsCorrect cost
    (domains (offeredBlocks data (fun root => xs.get (index root))) data.pending.partition.representative)
    Subtype.val result)

include hsound hsep hpos hHlarge hscale good hparts
omit hs hframe hr hH hinv

theorem ordinary_complement_small (j : ComponentBatch.Task data.pending hall cycle) (p i : Fin n) :
    (cost i).real ((xs.get (index (data.source (result.allocation.assigned j)))).piece p \
      PackageGeometry.proposalPiece (xs.get (index (data.source (result.allocation.assigned j)))).piece
        (fun p k => material (equalizerCache data (fun root => xs.get (index root)) (result.allocation.assigned j) p k))
        (ComponentDonors.ordinary data.pending data.visited data.frames Subtype.val
          (originalGaps data (fun root => xs.get (index root))) result j)
        (material (result.parts j).suffixParts) p) ≤ (n : ℝ)*(cost i).real R/H := by
  obtain ⟨U,hs⟩ := hsound (data.source (result.allocation.assigned j))
  apply proposal_complement_small cost hs (data.frames (result.allocation.assigned j))
    ((active_package_valid data _ cost _ H good _).live_good _ (good.live _))
    (fun i => (cost i).real R) H (fun i => (hpos i).le) (by linarith)
    data.component (data.frontier (result.allocation.assigned j)) (good.frontier _)
    _ rfl _ _ _ p i
  · intro p hp
    exact ComponentDonors.owner_other data.pending data.visited data.frames Subtype.val result j good.allowed p hp
  · intro i
    apply (measureReal_mono (μ := cost i) (ComponentPayments.suffix_subset cost _ Subtype.val
      data.pending.partition.representative result hparts j)).trans
    exact offered_small cost xs index cutter hsound R H hsep hpos hHlarge hscale data good hall
      (data.pending.partition.representative (j : Fin n)) (data.pending.partition.representative_mem _)
      (result.allocation.assigned j) i

end OpenGroup
end EnvyFreeResearch.Full.Chores.Outer
