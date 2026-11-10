import EnvyFreeResearch.Full.RefinedChoresTerminalCohortPrivate
import EnvyFreeResearch.Full.ChoresOuterResidueRemoval
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! Extracting the actual affine suffixes removes whole marked private
slots. The remaining residue is assembled without additional oracle calls. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentPieces Chores.ComponentExtraction ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n))

def TerminalGroup.marked : Finset (RootId × Fin n) :=
  Finset.univ.image (fun j : group.terminalClass.participants =>
    (data.source (group.roots (out.allocation.assigned j)),group.label))

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include good

theorem TerminalGroup.private_assigned (j : group.terminalClass.participants) :
    TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate
      (data.source (group.roots (out.allocation.assigned j))) group.label = (out.parts j).suffixParts := by
  rw [← good.source (group.roots (out.allocation.assigned j))]
  unfold TerminalGroup.poolPrivate
  have hp := ComponentPhysical.patch_live (data.frames ∘ group.roots) oldPrivate
    (TerminalGroup.nextPrivate data normal original r H group hr0 hH0 out)
    (fun a b h => group.roots.injective ((active_roots_injective data original cost r H good) h))
    (out.allocation.assigned j) group.label
  simp only [Function.comp_apply] at hp
  rw [hp]
  unfold TerminalGroup.nextPrivate
  rw [ComponentAssignment.dispatch_assigned]
  simp [proposalResidueCache,donorProposal,affineProposal]

theorem TerminalGroup.marked_exact :
    Outer.markedPrivate (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
      (TerminalGroup.marked data normal original r H group out) = extracted out := by
  ext x
  constructor
  · intro hx
    obtain ⟨slot,hslot⟩ := mem_iUnion.mp hx
    obtain ⟨hslot,hx⟩ := mem_iUnion.mp hslot
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hslot
    rw [TerminalGroup.private_assigned data normal original r H group hr0 hH0 out oldPrivate cost good] at hx
    exact mem_iUnion.mpr ⟨j,hx⟩
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨(data.source (group.roots (out.allocation.assigned j)),group.label),?_⟩
    apply mem_iUnion.mpr
    refine ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
    rw [TerminalGroup.private_assigned data normal original r H group hr0 hH0 out oldPrivate cost good]
    exact hj

variable (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
include hsound hparts hold hG

theorem TerminalGroup.private_subset (root : RootId) (a : Fin n) :
    material (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate root a) ⊆ G.piece root a := by
  rw [(TerminalGroup.pool_private_correct data normal original r H group hr0 hH0 out cost c hsound good hparts oldPrivate hold root a).2.2,hG]
  exact sdiff_subset

theorem TerminalGroup.remainder_cache_correct (R : Set ℝ) (R0 : List (Parent n))
    (hR : CacheValid (measureProfile cost) R R0) (hd : ∀ root a, Disjoint R (G.piece root a)) :
    CacheValid (measureProfile cost)
      ((R ∪ Outer.privateUnion (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) \ extracted out)
      (Outer.fullResidueCache R0 (Outer.removePrivate
        (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
        (TerminalGroup.marked data normal original r H group out))) := by
  rw [← TerminalGroup.marked_exact data normal original r H group hr0 hH0 out oldPrivate cost good]
  apply Outer.full_removed_cache_correct (measureProfile cost) G
    (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
    (TerminalGroup.marked data normal original r H group out)
  · intro root a
    have h := TerminalGroup.pool_private_correct data normal original r H group hr0 hH0 out cost c hsound good hparts oldPrivate hold root a
    exact ⟨h.1,h.2.1⟩
  · exact TerminalGroup.private_subset data normal original r H group hr0 hH0 out oldPrivate cost c hsound good hparts hold G hG
  · exact hR
  · exact hd

omit hr0 hH0 oldPrivate hold in
theorem TerminalGroup.extracted_cache_correct :
    CacheValid (measureProfile cost) (extracted out) (extractedCache out) := by
  apply Chores.ComponentExtraction.extracted_cache_correct Subtype.val (fun _ => group.label) out cost
    (TerminalGroup.blocks data normal original r H group) hparts
  intro s t hst p q
  have hne : (data.source (group.roots s),group.label) ≠ (data.source (group.roots t),group.label) :=
    fun he => hst (group.roots.injective (source_injective data original cost r H good (congrArg Prod.fst he)))
  apply (G.disjoint hne).mono
  · rw [hG]
    change TerminalGroup.blocks data normal original r H group s group.label ⊆ _
    rw [TerminalGroup.blocks_complement data normal original r H group cost c hsound s]
    exact sdiff_subset
  · rw [hG]
    change TerminalGroup.blocks data normal original r H group t group.label ⊆ _
    rw [TerminalGroup.blocks_complement data normal original r H group cost c hsound t]
    exact sdiff_subset

theorem TerminalGroup.extraction_partition (R : Set ℝ)
    (hd : ∀ root a, Disjoint R (G.piece root a)) :
    Disjoint (extracted out) (R ∪ Outer.privateUnion (Outer.removePrivate
      (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
      (TerminalGroup.marked data normal original r H group out))) ∧
    extracted out ∪ (R ∪ Outer.privateUnion (Outer.removePrivate
      (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
      (TerminalGroup.marked data normal original r H group out))) =
      R ∪ Outer.privateUnion (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate) := by
  let priv := TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate
  let marked := TerminalGroup.marked data normal original r H group out
  have hs := TerminalGroup.private_subset data normal original r H group hr0 hH0 out oldPrivate
    cost c hsound good hparts hold G hG
  have he := TerminalGroup.marked_exact data normal original r H group hr0 hH0 out oldPrivate cost good
  have hdis := Outer.marked_remainder_disjoint G priv marked hs
  rw [he] at hdis
  have hRx : Disjoint R (extracted out) := by
    rw [← he]
    apply disjoint_iUnion_right.mpr
    intro a
    apply disjoint_iUnion_right.mpr
    intro _
    exact (hd a.1 a.2).mono_right (hs a.1 a.2)
  refine ⟨disjoint_union_right.mpr ⟨hRx.symm,hdis⟩,?_⟩
  have hu := Outer.marked_remainder_partition priv marked
  rw [he] at hu
  rw [union_left_comm]
  exact congrArg (fun S => R ∪ S) hu

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.remainder_cache_correct
