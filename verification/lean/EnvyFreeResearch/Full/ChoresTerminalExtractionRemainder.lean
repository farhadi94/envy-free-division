import EnvyFreeResearch.Full.ChoresOuterComplement

/-! Removing the complete extracted suffixes leaves only small private
complements. This uses the actual final donor pieces, so it remains valid
when a reset reattaches earlier private material or the extracted set is large. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier
open ChoreComposition Outer
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

theorem proposal_complement_outside_extraction_small
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (hbefore : proposal.before=frame)
    (howner : ∀ p, p ≠ proposal.label → proposal.owner p ∈ frame.allowed p)
    (removed X : Set ℝ) (hremoved : removed ⊆ X) (p i : Fin n) :
    (cost i).real ((out.piece p \ PackageGeometry.proposalPiece out.piece
      (fun p j => material (out.equalizers (p,j)).parts.prefixParts) proposal removed p) \ X) ≤
        (n : ℝ)*r i/H := by
  unfold PackageGeometry.proposalPiece
  by_cases hexec : proposal.execute=true
  · rw [ite_eq_left hexec]
    by_cases hp : p=proposal.label
    · rw [ite_eq_left hp]
      have hempty : (out.piece p \ (out.piece p \ removed)) \ X=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxremoved : x ∈ removed := by
          by_contra hn
          exact hx.1.2 ⟨hx.1.1,hn⟩
        exact hx.2 (hremoved hxremoved)
      rw [hempty,measureReal_empty]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hr i)) hH.le
    · rw [ite_eq_right hp]
      exact (measureReal_mono (μ := cost i) sdiff_subset).trans
        (old_complement_small cost hs p r H _ _ _ _ (hinv p) hr hH _ (howner p hp) i)
  · rw [ite_eq_right hexec,hbefore]
    exact (measureReal_mono (μ := cost i) sdiff_subset).trans
      (old_complement_small cost hs p r H _ _ _ _ (hinv p) hr hH _ (hframe.1 p) i)

end EnvyFreeResearch.Full.Chores.Terminal
