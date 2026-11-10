import EnvyFreeResearch.Full.RefinedChoresTerminalCohortPool
import EnvyFreeResearch.Full.ChoresOuterPrivateCache
import EnvyFreeResearch.Full.RefinedChoresClosedCachesFrontier

/-! Literal complementary caches for terminal donors and the full pool.
No subtraction oracle or valuation-dependent reconstruction is used. -/
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

def TerminalGroup.equalizerSuffix (s : group.Root) (a j : Fin n) : List (Parent n) :=
  ((original (data.source (group.roots s))).equalizers (a,j)).parts.suffixParts

def TerminalGroup.nextPrivate (s : group.Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s a => TerminalGroup.equalizerSuffix data normal original r H group s a ((data.frames (group.roots s)).owner a))
    (fun j => proposalResidueCache (TerminalGroup.equalizerSuffix data normal original r H group (out.allocation.assigned j))
      (donorProposal group.terminalClass.participants group.label (data.frames ∘ group.roots)
        (TerminalGroup.path data normal original r H group hr0 hH0)
        (TerminalGroup.gaps data normal original r H group) out j) (out.parts j)) s

def TerminalGroup.poolPrivate (oldPrivate : RootId → Fin n → List (Parent n)) :=
  ComponentPhysical.patchCache (data.frames ∘ group.roots) oldPrivate
    (TerminalGroup.nextPrivate data normal original r H group hr0 hH0 out)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include hsound hparts

theorem TerminalGroup.donor_cache_correct (j : group.terminalClass.participants) (a : Fin n) :
    CacheValid (measureProfile cost)
      (PackageGeometry.proposalPiece (original (data.source (group.roots (out.allocation.assigned j)))).piece
        (fun a k => material (TerminalGroup.equalizer data normal original r H group (out.allocation.assigned j) a k))
        (donorProposal group.terminalClass.participants group.label (data.frames ∘ group.roots)
          (TerminalGroup.path data normal original r H group hr0 hH0)
          (TerminalGroup.gaps data normal original r H group) out j) (material (out.parts j).suffixParts) a)
      (donorCache group.terminalClass.participants group.label (data.frames ∘ group.roots)
        (TerminalGroup.path data normal original r H group hr0 hH0)
        (TerminalGroup.gaps data normal original r H group) out
        (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group) j a) :=
  RefinedChoresClosedCaches.donor_cache_correct group.terminalClass.participants group.label
    (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out
    (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group)
    cost (fun s => (original (data.source (group.roots s))).piece)
    (TerminalGroup.blocks data normal original r H group)
    (TerminalGroup.parent_unit data normal original r H group cost c hsound)
    (TerminalGroup.front_valid data normal original r H group cost c hsound)
    (TerminalGroup.equalizer_valid data normal original r H group cost c hsound)
    (TerminalGroup.front_subset data normal original r H group cost c hsound)
    (TerminalGroup.blocks_complement data normal original r H group cost c hsound) hparts j a

omit hparts in
theorem TerminalGroup.equalizer_private (s : group.Root) (a j : Fin n) :
    CacheValid (measureProfile cost)
      ((original (data.source (group.roots s))).piece a \ material (TerminalGroup.equalizer data normal original r H group s a j))
      (TerminalGroup.equalizerSuffix data normal original r H group s a j) :=
  Outer.private_equalizer cost _ c _ (hsound _).choose_spec a j

theorem TerminalGroup.next_private_correct (s : group.Root) (a : Fin n) :
    CacheValid (measureProfile cost)
      ((original (data.source (group.roots s))).piece a \
        material (TerminalGroup.next data normal original r H group hr0 hH0 out s a))
      (TerminalGroup.nextPrivate data normal original r H group hr0 hH0 out s a) := by
  unfold TerminalGroup.next nextCache TerminalGroup.nextPrivate ComponentAssignment.dispatch
  split
  next h =>
    have hc := TerminalGroup.donor_cache_correct data normal original r H group hr0 hH0 out cost c hsound hparts h.choose a
    rw [hc.2.2]
    have hsub := suffix_subset cost (TerminalGroup.blocks data normal original r H group)
      (Subtype.val : group.terminalClass.participants → Fin n) (fun _ => group.label) out hparts h.choose
    have hparent : material (out.parts h.choose).suffixParts ⊆
        (original (data.source (group.roots (out.allocation.assigned h.choose)))).piece group.label := by
      apply hsub.trans
      rw [TerminalGroup.blocks_complement data normal original r H group cost c hsound]
      exact sdiff_subset
    have hh := proposal_residue_cache_correct (measureProfile cost)
      (original (data.source (group.roots (out.allocation.assigned h.choose)))).piece
      (TerminalGroup.equalizer data normal original r H group (out.allocation.assigned h.choose))
      (TerminalGroup.equalizerSuffix data normal original r H group (out.allocation.assigned h.choose))
      (donorProposal group.terminalClass.participants group.label (data.frames ∘ group.roots)
        (TerminalGroup.path data normal original r H group hr0 hH0)
        (TerminalGroup.gaps data normal original r H group) out h.choose) (out.parts h.choose)
      (TerminalGroup.equalizer_private data normal original r H group cost c hsound _)
      ⟨(hparts h.choose).2.1,(hparts h.choose).2.2.1,rfl⟩ hparent a
    simpa only [h.choose_spec] using hh
  next h => exact TerminalGroup.equalizer_private data normal original r H group cost c hsound s a _

include good

theorem TerminalGroup.pool_private_correct (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate) :
    Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      (TerminalGroup.poolCache data normal original r H group hr0 hH0 out)
      (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate) := by
  apply Outer.private_patch (data.frames ∘ group.roots) (measureProfile cost)
    (fun root => (original root).piece) data.cache oldPrivate
    (TerminalGroup.next data normal original r H group hr0 hH0 out)
    (TerminalGroup.nextPrivate data normal original r H group hr0 hH0 out) hold
  intro s a
  simpa only [Function.comp_apply,good.source] using
    TerminalGroup.next_private_correct data normal original r H group hr0 hH0 out cost c hsound hparts s a

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.pool_private_correct
