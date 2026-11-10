import EnvyFreeResearch.Full.RefinedChoresGroupCaches
import EnvyFreeResearch.Full.RefinedChoresDonorOrigins

/-! Concrete ordinary root-local update. The stored pool is built from the
actual SubCore output and its physical caches; no post-state certificate
is assumed. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open ChoreComposition RefinedChoresPhysicalPayment RefinedChoresDonorCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)
    (out : Result (Root := group.Root) group.component)

def Group.commit : Data n RootId := commitOpen data group.roots
  (Group.liveOutput data normal original r H group out) (Group.next data normal original r H group out)

theorem Group.commit_decreases : (Group.commit data normal original r H group out).size < data.size := by
  apply RefinedChoresData.commit_decreases
  have h := Finset.card_pos.mpr (Group.nonempty data normal original r H group)
  simp only [Fintype.card_fin]
  omega

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : ComponentRecording.PartsCorrect cost
      (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include good

theorem Group.survivor_cache (a : Fin n) :
    Group.next data normal original r H group out (Group.survivor data normal original r H group out) a =
      ((original (data.source (group.roots (Group.survivor data normal original r H group out)))).equalizers (a,a)).parts.prefixParts := by
  unfold Group.next nextCache Group.survivor
  rw [ComponentAssignment.dispatch_unassigned _ _ _ _ (ComponentAssignment.unused_spec _ _)]
  simp only [Function.comp_apply,(data.tracked _).owner_identity,Equiv.Perm.one_apply,Group.equalizer]

include hsound hparts

theorem Group.commit_good
    (hvalid : (Group.output data normal original r H group out).Valid)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
    (hsmall : ∀ s i, (cost i).real (Group.blocks data normal original r H group s group.label) ≤ (n:ℝ)*r i/H) :
    (Group.commit data normal original r H group out).Good original cost r H := by
  refine RefinedChoresData.commit_good data group.roots (Group.liveOutput data normal original r H group out)
    (Group.next data normal original r H group out) original cost r H good
    (Group.liveOutput_good data normal original r H group cost good out hvalid hr hH)
    (Group.output_ids data normal original r H group cost good out)
    (Group.next_valid data normal original r H group cost c hsound out hparts)
    (Group.next_subset data normal original r H group cost c hsound out hparts)
    (fun s a i => Group.next_complement_small data normal original r H group cost c hsound good out hparts hr hH hsmall s a i)
    ?_ (nextAllocation group.component group.label (data.frames ∘ group.roots) group.path
      (Group.gaps data normal original r H group) out) ?_ ?_ ?_
  · intro a
    change patchedCache data group.roots (Group.next data normal original r H group out)
      (data.source (group.roots (Group.survivor data normal original r H group out))) a = _
    rw [patch_on data original cost r H good]
    exact Group.survivor_cache data normal original r H group out cost good a
  · intro s
    exact (next_allocation_root group.component group.label (data.frames ∘ group.roots) group.path
      (Group.gaps data normal original r H group) out s).trans (good.source _)
  · exact Group.next_cost data normal original r H group cost c hsound good out hparts
  · intro a ha
    rcases RefinedChoresDonorOrigins.output_allocation_member group.component group.label
      (data.frames ∘ group.roots) group.path (data.packages ∘ group.roots)
      (Group.gaps data normal original r H group) out group.target (by simp [Group.Root])
      (fun s => good.live _) a ha with ⟨s,hs⟩ | ⟨s,hs⟩
    · exact Or.inr (Or.inl ⟨group.roots s,hs⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨s,hs⟩))

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.commit_good
