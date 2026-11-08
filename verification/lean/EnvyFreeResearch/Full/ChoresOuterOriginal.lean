import EnvyFreeResearch.Full.ChoresFrontierInterface
import EnvyFreeResearch.Full.ChoresComponentFrontierValues

/-! Immutable original snapshot data supplies the geometric and numerical
hypotheses of a physical compensation group. These identities are derived
from recorded equalizers and survive every frame advance. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier
open ChoreComposition Scheduler Components
open scoped Classical

variable {n : ℕ} {RootId Root : Type*}

structure OriginalFrame (frame : Frame (Fin n) RootId) (out : Snapshot.Output n) : Prop where
  baseline : frame.baseline=baselines out.parents
  values : frame.equalizerCost=fun i p j => (out.equalizers (p,j)).values i

theorem initial_original (root : RootId) (out : Snapshot.Output n) :
    OriginalFrame (PackageGeometry.initialFrame root out.parents out.equalizers) out := ⟨rfl,rfl⟩

theorem advance_original (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
    (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
    (frames : Root → Frame (Fin n) RootId) (original : Root → Snapshot.Output n)
    (h : ∀ s, OriginalFrame (frames s) (original s)) (s : Root) :
    OriginalFrame (ComponentFrames.advance state hall cycle visited frames s) (original s) :=
  ⟨(h s).baseline,(h s).values⟩

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Snapshot.Output n}
  (hs : Snapshot.Sound cost U c out)
  (frame : Frame (Fin n) RootId) (hf : OriginalFrame frame out)

include hs hf

theorem original_equalizer_value (i p j : Fin n) :
    frame.equalizerCost i p j=(cost i).real (material (out.equalizers (p,j)).parts.prefixParts) := by
  rw [hf.values,(snapshot_equalizers hs p j).2.1.2.2]
  exact (snapshot_equalizers hs p j).2.2.2.2 i

theorem original_equalized (p i : Fin n) : frame.equalizerCost i p i=frame.baseline i := by
  rw [hf.values,hf.baseline]
  exact ((snapshot_equalizers hs p i).2.2.2.2 i).trans (snapshot_equalizers hs p i).2.2.2.1

theorem original_gap (p i : Fin n) :
    Clearance.gap out i p=(cost i).real (out.piece p)-frame.baseline i := by
  simp only [Clearance.gap_physical hs,hf.baseline,baselines,Output.piece,
    material_value cost _ (hs.parent_cache i).1 (hs.parent_cache i).2.1]

omit hf in
theorem original_equalizer_subset (p j : Fin n) :
    material (out.equalizers (p,j)).parts.prefixParts ⊆ out.piece p := by
  rw [(snapshot_equalizers hs p j).2.1.2.2]
  exact inter_subset_left

theorem original_frontier_gap (p q i : Fin n) :
    frame.gap i q p=(cost i).real (material (out.equalizers (p,q)).parts.suffixParts)-Clearance.gap out i p := by
  apply ComponentFrames.original_frontier_value cost frame out.piece
    (fun p q => material (out.equalizers (p,q)).parts.prefixParts)
    (material (out.equalizers (p,q)).parts.suffixParts) (fun i => Clearance.gap out i p) p q
  · exact original_equalizer_subset cost hs p q
  · exact material_measurable _
  · exact offer_complement cost (out.piece p) (out.parents p) (snapshot_parent_cache hs p)
      out.equalizers p (baselines out.parents) (snapshot_equalizers hs p) (hs.own_equalizers p).1 (.outside q)
  · exact fun i => original_equalizer_value cost hs frame hf i p q
  · exact fun i => original_gap cost hs frame hf p i

omit hf in
/-- The entire old private complement is small, not just material newly
removed in a particular compensation call. -/
theorem old_complement_small (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C A F : Finset (Fin n)) (z : Fin n)
    (hinv : Invariant (weight out.equalizers p) (rankOf out.equalizers p) r H
      (eligible (weight out.equalizers p) (rankOf out.equalizers p) r H) C A F z)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) (j : Fin n) (hj : j ∈ A) (i : Fin n) :
    (cost i).real (out.piece p \ material (out.equalizers (p,j)).parts.prefixParts) ≤ (n : ℝ)*r i/H := by
  have hcomp := offer_complement cost (out.piece p) (out.parents p) (snapshot_parent_cache hs p)
    out.equalizers p (baselines out.parents) (snapshot_equalizers hs p) (hs.own_equalizers p).1 (.outside j)
  have hv := offer_value cost (out.piece p) (out.parents p) (snapshot_parent_cache hs p)
    out.equalizers p (baselines out.parents) (snapshot_equalizers hs p) (hs.own_equalizers p).1 (.outside j) i
  simp only [Outcome.offer,Outcome.front] at hcomp
  simp only [Outcome.offer,Outcome.boundary] at hv
  rw [← hcomp,hv]
  apply tail_small (weight out.equalizers p) i (rankOf out.equalizers p j) (r i) H (hr i) hH
  intro a ha
  exact hinv.passed_small a ((hinv.allowed_above j hj).trans ha) i

theorem original_contained_gap (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C A F : Finset (Fin n)) (z q : Fin n)
    (hinv : Invariant (weight out.equalizers p) (rankOf out.equalizers p) r H
      (eligible (weight out.equalizers p) (rankOf out.equalizers p) r H) C A F z)
    (hstop : (Stop.outside q).Valid (rankOf out.equalizers p)
      (eligible (weight out.equalizers p) (rankOf out.equalizers p) r H) C)
    (j : Fin n) (hj : j ∈ A) (i : Fin n) : frame.gap i j p ≤ frame.gap i q p := by
  apply ComponentFrames.contained_frontier_gap cost frame
    (fun p j => material (out.equalizers (p,j)).parts.prefixParts) p q j i
  · exact outside_old_equalizers_contain cost (out.piece p) (out.parents p) (snapshot_parent_cache hs p)
      out.equalizers p (baselines out.parents) (snapshot_equalizers hs p) (hs.own_equalizers p).1
      r H C A F z q hinv hstop j hj
  · exact fun k => original_equalizer_value cost hs frame hf i p k

end EnvyFreeResearch.Full.Chores.Outer
