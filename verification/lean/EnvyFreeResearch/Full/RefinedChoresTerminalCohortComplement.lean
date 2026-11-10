import EnvyFreeResearch.Full.RefinedChoresTerminalCohortPrivate

/-! Full private-slot bounds for the terminal pool, including untouched
roots and frozen ancestors. Atomic extraction is removed literally. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentPieces ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include hsound good hparts

theorem TerminalGroup.next_complement_small
    (hsmall : ∀ s i, (cost i).real (TerminalGroup.blocks data normal original r H group s group.label) ≤ (n:ℝ)*r i/H)
    (s : group.Root) (a i : Fin n) :
    (cost i).real ((original (data.source (group.roots s))).piece a \
      material (TerminalGroup.next data normal original r H group hr0 hH0 out s a)) ≤ (n:ℝ)*r i/H := by
  apply ComponentAssignment.dispatch_property out.allocation
    (fun s a => TerminalGroup.equalizer data normal original r H group s a ((data.frames (group.roots s)).owner a))
    (fun j => donorCache group.terminalClass.participants group.label (data.frames ∘ group.roots)
      (TerminalGroup.path data normal original r H group hr0 hH0)
      (TerminalGroup.gaps data normal original r H group) out
      (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group) j)
    (fun s cache => (cost i).real ((original (data.source (group.roots s))).piece a \ material (cache a)) ≤ (n:ℝ)*r i/H)
  · intro t
    have h := good.complement_small (data.source (group.roots t)) a i
    rw [good.live_cache] at h
    simpa only [(data.tracked (group.roots t)).owner_identity,Equiv.Perm.one_apply,TerminalGroup.equalizer] using h
  · intro j
    rw [(TerminalGroup.donor_cache_correct data normal original r H group hr0 hH0 out cost c hsound hparts j a).2.2]
    apply RefinedChoresClosedCaches.proposal_complement_small data original cost r H good c hsound hr0 hH0
      (group.roots (out.allocation.assigned j))
      ((active_package_valid data original cost r H good _).live_good _ (good.live _))
      _ rfl _ _ _ a i
    · intro b hb
      change owners group.terminalClass.participants group.label (data.frames ∘ group.roots)
        (TerminalGroup.path data normal original r H group hr0 hH0) out j b ∈
          (data.frames (group.roots (out.allocation.assigned j))).allowed b
      simp only [owners,dite_eq_left j.property]
      apply RefinedChoresDirectedMatching.donor_allowed_other
      · intro a
        exact ((data.tracked (group.roots (out.allocation.assigned j))).exact a a).mpr
          (RefinedChoresPartialGraph.allowed_refl _ _ a)
      · exact hb
    · intro k
      exact (measureReal_mono (μ := cost k) (suffix_subset cost
        (TerminalGroup.blocks data normal original r H group) Subtype.val (fun _ => group.label) out hparts j)).trans
          (hsmall (out.allocation.assigned j) k)

theorem TerminalGroup.next_complement_outside_small
    (X : Set ℝ) (hX : ∀ j : group.terminalClass.participants, material (out.parts j).suffixParts ⊆ X)
    (s : group.Root) (a i : Fin n) :
    (cost i).real (((original (data.source (group.roots s))).piece a \
      material (TerminalGroup.next data normal original r H group hr0 hH0 out s a)) \ X) ≤ (n:ℝ)*r i/H := by
  apply ComponentAssignment.dispatch_property out.allocation
    (fun s a => TerminalGroup.equalizer data normal original r H group s a ((data.frames (group.roots s)).owner a))
    (fun j => donorCache group.terminalClass.participants group.label (data.frames ∘ group.roots)
      (TerminalGroup.path data normal original r H group hr0 hH0)
      (TerminalGroup.gaps data normal original r H group) out
      (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group) j)
    (fun s cache => (cost i).real (((original (data.source (group.roots s))).piece a \ material (cache a)) \ X) ≤ (n:ℝ)*r i/H)
  · intro t
    apply (measureReal_mono (μ := cost i) sdiff_subset).trans
    have h := good.complement_small (data.source (group.roots t)) a i
    rw [good.live_cache] at h
    simpa only [(data.tracked (group.roots t)).owner_identity,Equiv.Perm.one_apply,TerminalGroup.equalizer] using h
  · intro j
    rw [(TerminalGroup.donor_cache_correct data normal original r H group hr0 hH0 out cost c hsound hparts j a).2.2]
    apply RefinedChoresClosedCaches.proposal_complement_outside_extraction_small data original cost r H good c hsound hr0 hH0
      (group.roots (out.allocation.assigned j))
      ((active_package_valid data original cost r H good _).live_good _ (good.live _))
      _ rfl _ _ X (hX j) a i
    intro b hb
    change owners group.terminalClass.participants group.label (data.frames ∘ group.roots)
      (TerminalGroup.path data normal original r H group hr0 hH0) out j b ∈
        (data.frames (group.roots (out.allocation.assigned j))).allowed b
    simp only [owners,dite_eq_left j.property]
    apply RefinedChoresDirectedMatching.donor_allowed_other
    · intro a
      exact ((data.tracked (group.roots (out.allocation.assigned j))).exact a a).mpr
        (RefinedChoresPartialGraph.allowed_refl _ _ a)
    · exact hb

variable (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate)
include hold

theorem TerminalGroup.pool_private_small
    (hsmall : ∀ s i, (cost i).real (TerminalGroup.blocks data normal original r H group s group.label) ≤ (n:ℝ)*r i/H)
    (root : RootId) (a i : Fin n) :
    (cost i).real (material (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate root a)) ≤ (n:ℝ)*r i/H := by
  unfold TerminalGroup.poolPrivate ComponentPhysical.patchCache
  split
  next h =>
    rw [(TerminalGroup.next_private_correct data normal original r H group hr0 hH0 out cost c hsound hparts h.choose a).2.2]
    exact TerminalGroup.next_complement_small data normal original r H group hr0 hH0 out cost c hsound good hparts hsmall h.choose a i
  next h =>
    rw [(hold root a).2.2]
    exact good.complement_small root a i

theorem TerminalGroup.pool_private_outside_small
    (X : Set ℝ) (hX : ∀ j : group.terminalClass.participants, material (out.parts j).suffixParts ⊆ X)
    (root : RootId) (a i : Fin n) :
    (cost i).real (material (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate root a) \ X) ≤ (n:ℝ)*r i/H := by
  unfold TerminalGroup.poolPrivate ComponentPhysical.patchCache
  split
  next h =>
    rw [(TerminalGroup.next_private_correct data normal original r H group hr0 hH0 out cost c hsound hparts h.choose a).2.2]
    exact TerminalGroup.next_complement_outside_small data normal original r H group hr0 hH0 out cost c hsound good hparts X hX h.choose a i
  next h =>
    rw [(hold root a).2.2]
    exact (measureReal_mono (μ := cost i) sdiff_subset).trans (good.complement_small root a i)

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.pool_private_outside_small
