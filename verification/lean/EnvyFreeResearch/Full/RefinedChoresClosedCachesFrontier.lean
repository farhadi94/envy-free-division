import EnvyFreeResearch.Full.RefinedChoresData
import EnvyFreeResearch.Full.ChoresOuterComplement
import EnvyFreeResearch.Full.ChoresTerminalExtractionRemainder

/-! Every physically allowed equalizer remains small in a root-local
pending state, even before its paid target has joined the current SCC. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresClosedCaches
open Set MeasureTheory IntervalOracle ChoreComposition
open Chores Chores.InitialPartition Chores.OrderedUnion Chores.Frontier
open RefinedChoresData
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
include good

theorem frontier_invariant_univ (s : Fin data.size) (p : Fin n) :
    Frontier.Invariant
      (Frontier.weight (original (data.source s)).equalizers p)
      (Frontier.rankOf (original (data.source s)).equalizers p) r H
      (Frontier.eligible (Frontier.weight (original (data.source s)).equalizers p)
        (Frontier.rankOf (original (data.source s)).equalizers p) r H)
      Finset.univ ((data.frames s).allowed p) ((data.frames s).forbidden p) (data.frontier s p) :=
  RefinedChoresPendingFrontier.absorb _ _ _ _ _ _ _ _ _ _ (good.frontier s p)
    (Finset.subset_univ _) (Finset.mem_univ _)

variable (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
include hsound hr hH

theorem allowed_complement_small (s : Fin data.size) (p j i : Fin n)
    (hj : j ∈ (data.frames s).allowed p) :
    (cost i).real ((original (data.source s)).piece p \
      material ((original (data.source s)).equalizers (p,j)).parts.prefixParts) ≤
        (n : ℝ)*r i/H :=
  Outer.old_complement_small cost (hsound (data.source s)).choose_spec p r H _ _ _ _
    (frontier_invariant_univ data original cost r H good s p) hr hH j hj i

/-- Actual terminal proposal output, including all old private pieces. -/
theorem proposal_complement_small (s : Fin data.size)
    (hframe : (data.frames s).Good)
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (hbefore : proposal.before=data.frames s)
    (howner : ∀ p, p ≠ proposal.label → proposal.owner p ∈ (data.frames s).allowed p)
    (removed : Set ℝ) (hsmall : ∀ i, (cost i).real removed ≤ (n : ℝ)*r i/H)
    (p i : Fin n) :
    (cost i).real ((original (data.source s)).piece p \
      PackageGeometry.proposalPiece (original (data.source s)).piece
        (fun p j => material ((original (data.source s)).equalizers (p,j)).parts.prefixParts)
        proposal removed p) ≤ (n : ℝ)*r i/H :=
  Outer.proposal_complement_small cost (hsound (data.source s)).choose_spec (data.frames s)
    hframe r H hr hH (fun _ => Finset.univ) (data.frontier s)
    (frontier_invariant_univ data original cost r H good s) proposal hbefore howner removed hsmall p i

/-- For an atomic outcome, the same full complement is small after
excluding the literal union of recorded extracted suffixes. -/
theorem proposal_complement_outside_extraction_small (s : Fin data.size)
    (hframe : (data.frames s).Good)
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (hbefore : proposal.before=data.frames s)
    (howner : ∀ p, p ≠ proposal.label → proposal.owner p ∈ (data.frames s).allowed p)
    (removed X : Set ℝ) (hremoved : removed ⊆ X) (p i : Fin n) :
    (cost i).real (((original (data.source s)).piece p \
      PackageGeometry.proposalPiece (original (data.source s)).piece
        (fun p j => material ((original (data.source s)).equalizers (p,j)).parts.prefixParts)
        proposal removed p) \ X) ≤ (n : ℝ)*r i/H :=
  Terminal.proposal_complement_outside_extraction_small cost (hsound (data.source s)).choose_spec
    (data.frames s) hframe r H hr hH (fun _ => Finset.univ) (data.frontier s)
    (frontier_invariant_univ data original cost r H good s) proposal hbefore howner removed X hremoved p i

end EnvyFreeResearch.Full.RefinedChoresClosedCaches
#print axioms EnvyFreeResearch.Full.RefinedChoresClosedCaches.proposal_complement_small
#print axioms EnvyFreeResearch.Full.RefinedChoresClosedCaches.proposal_complement_outside_extraction_small
