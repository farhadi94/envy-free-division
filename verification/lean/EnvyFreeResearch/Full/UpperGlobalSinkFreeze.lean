import EnvyFreeResearch.Full.UpperGlobalSinkGraph

/-! Actual sink freezing changes only the active set. Cake freezes the
sink; chores retain it. Cross-boundary guards follow from absent cached edges. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Sink
open Set MeasureTheory UpperGlobalPhysical GlobalCompletion
open scoped Classical
variable {n : ℕ}

def retained (direction : Direction) (A S : Finset (Fin n)) : Finset (Fin n) :=
  match direction with
  | .cake => A \ S
  | .chore => S

theorem outside_exists (A S : Finset (Fin n)) (hsub : S ⊆ A) (hne : S ≠ A) :
    ∃ j, j ∈ A ∧ j ∉ S := by
  by_contra! h
  exact hne (Finset.Subset.antisymm hsub h)

theorem retained_subset (direction : Direction) (A S : Finset (Fin n)) (hs : S ⊆ A) :
    retained direction A S ⊆ A := by
  cases direction with
  | cake => exact Finset.sdiff_subset
  | chore => exact hs

theorem retained_progress (direction : Direction) (E : Fin n → Fin n → Prop)
    (A S : Finset (Fin n)) (hs : ProperSink E A S) :
    (retained direction A S).Nonempty ∧ ∃ i, i ∈ A ∧ i ∉ retained direction A S := by
  obtain ⟨i,hi⟩ := hs.1
  obtain ⟨j,hj,hjS⟩ := outside_exists A S hs.2.1 hs.2.2.1
  cases direction with
  | cake => exact ⟨⟨j,Finset.mem_sdiff.mpr ⟨hj,hjS⟩⟩,i,hs.2.1 hi,
      fun h => (Finset.mem_sdiff.mp h).2 hi⟩
  | chore => exact ⟨hs.1,j,hj,hjS⟩

theorem sink_cross_dominates (a : Anchor n) (direction : Direction) (S : Finset (Fin n))
    (hs : ProperSink (a.edge direction) a.active S)
    (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ a.active) (hjS : j ∉ S) :
    j ≠ i ∧ a.cachedResidue i ≤ margin direction a.cachedValue i j := by
  have hne : j ≠ i := fun h => hjS (h.symm ▸ hi)
  refine ⟨hne,le_of_not_gt ?_⟩
  intro hlt
  exact hjS (hs.2.2.2 i hi j hj ⟨hs.2.1 hi,hj,hne,hlt⟩)

theorem cached_freeze_separation (a : Anchor n) (direction : Direction) (S : Finset (Fin n))
    (hs : ProperSink (a.edge direction) a.active S) :
    FreezeSeparation direction a.cachedValue (↑a.active) (↑(retained direction a.active S)) a.cachedResidue := by
  cases direction with
  | cake =>
    intro f hf hfr i hi
    have hi' := Finset.mem_sdiff.mp hi
    have hfS : f ∈ S := by
      by_contra hnot
      exact hfr (Finset.mem_sdiff.mpr ⟨hf,hnot⟩)
    exact (sink_cross_dominates a .cake S hs f hfS i hi'.1 hi'.2).2
  | chore =>
    intro i hi f hf hfS
    exact (sink_cross_dominates a .chore S hs i hi f hf hfS).2

def freezeAnchor (a : Anchor n) (direction : Direction) (S : Finset (Fin n)) : Anchor n :=
  { a with active := retained direction a.active S }

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
  (direction : Direction) (S : Finset (Fin n))
  (hs : ProperSink (a.edge direction) a.active S)

theorem freeze_physical (ha : a.Physical μ whole) : (freezeAnchor a direction S).Physical μ whole := by
  exact ⟨ha.bundles_wellFormed,ha.residue_wellFormed,ha.pairwise,ha.separate,ha.cover⟩

include hs in
theorem freeze_separation (ha : a.Physical μ whole) :
    FreezeSeparation direction (a.table μ).value (a.table μ).active
      ((freezeAnchor a direction S).table μ).active (a.table μ).residue := by
  have h := cached_freeze_separation a direction S hs
  rw [cachedValue_correct μ whole a ha,cachedResidue_correct μ whole a ha] at h
  exact h

include hs in
def freeze_event (ha : a.Physical μ whole) :
    CompletionEvent direction (a.table μ) ((freezeAnchor a direction S).table μ) := by
  refine CompletionEvent.freeze (before := a.table μ)
    (after := (freezeAnchor a direction S).table μ) rfl rfl ?_ ?_ ?_
  · exact retained_subset direction a.active S hs.2.1
  · exact (retained_progress direction (a.edge direction) a.active S hs).2
  · exact freeze_separation μ whole a direction S hs ha

include hs in
theorem freeze_committed (ha : a.Committed μ direction whole) :
    (freezeAnchor a direction S).Committed μ direction whole := by
  refine ⟨freeze_physical μ whole a direction S ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,?_⟩
  exact freeze_preserves_guard direction (a.table μ).value (a.table μ).active
    ((freezeAnchor a direction S).table μ).active (a.table μ).residue
    (retained_subset direction a.active S hs.2.1) ha.2.2.2.2
    (freeze_separation μ whole a direction S hs ha.1)
end EnvyFreeResearch.Full.UpperGlobal.Sink
