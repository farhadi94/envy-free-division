import EnvyFreeResearch.Full.RefinedChoresGroupCommit
import EnvyFreeResearch.Full.ChoresOuterPrivateCache

/-! Literal complementary caches for ordinary donors and the full pool.
No subtraction oracle or valuation-dependent reconstruction is used. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentPieces ChoreComposition
open RefinedChoresPhysicalPayment RefinedChoresDonorCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)
    (out : Result (Root := group.Root) group.component)

def Group.equalizerSuffix (s : group.Root) (a j : Fin n) : List (Parent n) :=
  ((original (data.source (group.roots s))).equalizers (a,j)).parts.suffixParts

def Group.nextPrivate (s : group.Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s a => Group.equalizerSuffix data normal original r H group s a ((data.frames (group.roots s)).owner a))
    (fun j => proposalResidueCache (Group.equalizerSuffix data normal original r H group (out.allocation.assigned j))
      (donorProposal group.component group.label (data.frames ∘ group.roots)
        (Group.path data normal original r H group)
        (Group.gaps data normal original r H group) out j) (out.parts j)) s

def Group.poolPrivate (oldPrivate : RootId → Fin n → List (Parent n)) :=
  ComponentPhysical.patchCache (data.frames ∘ group.roots) oldPrivate
    (Group.nextPrivate data normal original r H group out)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (Group.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include hsound hparts

theorem Group.donor_cache_correct (j : group.component) (a : Fin n) :
    CacheValid (measureProfile cost)
      (PackageGeometry.proposalPiece (original (data.source (group.roots (out.allocation.assigned j)))).piece
        (fun a k => material (Group.equalizer data normal original r H group (out.allocation.assigned j) a k))
        (donorProposal group.component group.label (data.frames ∘ group.roots)
          (Group.path data normal original r H group)
          (Group.gaps data normal original r H group) out j) (material (out.parts j).suffixParts) a)
      (donorCache group.component group.label (data.frames ∘ group.roots)
        (Group.path data normal original r H group)
        (Group.gaps data normal original r H group) out
        (Group.equalizer data normal original r H group) (Group.front data normal original r H group) j a) :=
  RefinedChoresDonorCaches.donor_cache_correct group.component group.label
    (data.frames ∘ group.roots) (Group.path data normal original r H group)
    (Group.gaps data normal original r H group) out
    (Group.equalizer data normal original r H group) (Group.front data normal original r H group)
    cost (fun s => (original (data.source (group.roots s))).piece)
    (Group.blocks data normal original r H group)
    (Group.parent_unit data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_valid data normal original r H group cost c hsound s a (group.target s))
    (Group.equalizer_valid data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_subset data normal original r H group cost c hsound s a (group.target s))
    (Group.blocks_complement data normal original r H group cost c hsound) hparts j a

omit hparts in
theorem Group.equalizer_private (s : group.Root) (a j : Fin n) :
    CacheValid (measureProfile cost)
      ((original (data.source (group.roots s))).piece a \ material (Group.equalizer data normal original r H group s a j))
      (Group.equalizerSuffix data normal original r H group s a j) :=
  Outer.private_equalizer cost _ c _ (hsound _).choose_spec a j

theorem Group.next_private_correct (s : group.Root) (a : Fin n) :
    CacheValid (measureProfile cost)
      ((original (data.source (group.roots s))).piece a \
        material (Group.next data normal original r H group out s a))
      (Group.nextPrivate data normal original r H group out s a) := by
  unfold Group.next nextCache Group.nextPrivate ComponentAssignment.dispatch
  split
  next h =>
    have hc := Group.donor_cache_correct data normal original r H group out cost c hsound hparts h.choose a
    rw [hc.2.2]
    have hsub := suffix_subset cost (Group.blocks data normal original r H group)
      (Subtype.val : group.component → Fin n) (fun _ => group.label) out hparts h.choose
    have hparent : material (out.parts h.choose).suffixParts ⊆
        (original (data.source (group.roots (out.allocation.assigned h.choose)))).piece group.label := by
      apply hsub.trans
      rw [Group.blocks_complement data normal original r H group cost c hsound]
      exact sdiff_subset
    have hh := proposal_residue_cache_correct (measureProfile cost)
      (original (data.source (group.roots (out.allocation.assigned h.choose)))).piece
      (Group.equalizer data normal original r H group (out.allocation.assigned h.choose))
      (Group.equalizerSuffix data normal original r H group (out.allocation.assigned h.choose))
      (donorProposal group.component group.label (data.frames ∘ group.roots)
        (Group.path data normal original r H group)
        (Group.gaps data normal original r H group) out h.choose) (out.parts h.choose)
      (Group.equalizer_private data normal original r H group cost c hsound _)
      ⟨(hparts h.choose).2.1,(hparts h.choose).2.2.1,rfl⟩ hparent a
    simpa only [h.choose_spec] using hh
  next h => exact Group.equalizer_private data normal original r H group cost c hsound s a _

include good

theorem Group.pool_private_correct (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate) :
    Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      ((Group.commit data normal original r H group out).cache)
      (Group.poolPrivate data normal original r H group out oldPrivate) := by
  apply Outer.private_patch (data.frames ∘ group.roots) (measureProfile cost)
    (fun root => (original root).piece) data.cache oldPrivate
    (Group.next data normal original r H group out)
    (Group.nextPrivate data normal original r H group out) hold
  intro s a
  simpa only [Function.comp_apply,good.source] using
    Group.next_private_correct data normal original r H group out cost c hsound hparts s a

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.pool_private_correct
