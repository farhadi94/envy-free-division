import EnvyFreeResearch.Full.RefinedChoresTerminalCohortExtraction
import EnvyFreeResearch.Full.ChoresOuterResiduePartition

/-! The terminal cohort's actual closed allocation and complementary local
 domain. Every original root is included exactly once. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)

def TerminalGroup.base : Completion.Allocation n (Fin n) :=
  Outer.poolAllocation (TerminalGroup.pool data normal original r H group hr0 hH0 out)
    (TerminalGroup.poolCache data normal original r H group hr0 hH0 out)

def TerminalGroup.allocated : Set ℝ :=
  Outer.poolDomain (TerminalGroup.pool data normal original r H group hr0 hH0 out)
    (TerminalGroup.poolCache data normal original r H group hr0 hH0 out)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (hcorrect : PhysicalCorrect (affineUtility cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation)
    (hvalid : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
include hsound good hparts hcorrect hvalid hG

theorem TerminalGroup.base_sound :
    (TerminalGroup.base data normal original r H group hr0 hH0 out).Sound cost id
      (TerminalGroup.allocated data normal original r H group hr0 hH0 out) := by
  exact Outer.pool_allocation_sound _
    (TerminalGroup.pool_valid data normal original r H group hr0 hH0 out cost good hvalid)
    ((TerminalGroup.pool_ids data normal original r H group hr0 hH0 out cost good hparts hcorrect).nodup_iff.mpr
      (Finset.nodup_toList _)) G _
    (fun root a => by rw [hG]; exact TerminalGroup.pool_cache_subset data normal original r H group hr0 hH0 out cost c hsound good hparts root a)
    cost (TerminalGroup.pool_cache_valid data normal original r H group hr0 hH0 out cost c hsound good hparts)
    (TerminalGroup.pool_realizes data normal original r H group hr0 hH0 out cost c hsound good hparts)

omit hsound hvalid hG in
theorem TerminalGroup.allocated_exact :
    TerminalGroup.allocated data normal original r H group hr0 hH0 out =
      Outer.privateUnion (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) :=
  Outer.pool_domain_all_roots _ _
    (TerminalGroup.pool_ids data normal original r H group hr0 hH0 out cost good hparts hcorrect)

omit hvalid in
theorem TerminalGroup.base_material (i : Fin n) :
    material ((TerminalGroup.base data normal original r H group hr0 hH0 out).pieces i) =
      ComponentPhysical.bundle (Outer.closePool
        (TerminalGroup.pool data normal original r H group hr0 hH0 out))
        (TerminalGroup.poolCache data normal original r H group hr0 hH0 out) i := by
  apply (ComponentPhysical.bundle_cache_correct _ ?_ G _ ?_ (measureProfile cost) ?_ i).2.2
  · rw [Outer.close_pool_ids]
    exact (TerminalGroup.pool_ids data normal original r H group hr0 hH0 out cost good hparts hcorrect).nodup_iff.mpr
      (Finset.nodup_toList _)
  · intro root a
    rw [hG]
    exact TerminalGroup.pool_cache_subset data normal original r H group hr0 hH0 out cost c hsound good hparts root a
  · exact TerminalGroup.pool_cache_valid data normal original r H group hr0 hH0 out cost c hsound good hparts

variable (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate)
include hold
omit hvalid in
theorem TerminalGroup.domain_partition (R : Set ℝ) (hd : ∀ root a, Disjoint R (G.piece root a)) :
    Disjoint (TerminalGroup.allocated data normal original r H group hr0 hH0 out)
      (R ∪ Outer.privateUnion (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) ∧
    TerminalGroup.allocated data normal original r H group hr0 hH0 out ∪
      (R ∪ Outer.privateUnion (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) =
        R ∪ ⋃ root, ⋃ a, G.piece root a := by
  let retained := TerminalGroup.poolCache data normal original r H group hr0 hH0 out
  let priv := TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate
  have hp : Outer.PrivateCorrect (measureProfile cost) G.piece retained priv := by
    intro root a
    rw [hG]
    exact TerminalGroup.pool_private_correct data normal original r H group hr0 hH0 out
      cost c hsound good hparts oldPrivate hold root a
  have hs : ∀ root a, material (retained root a) ⊆ G.piece root a := by
    intro root a
    rw [hG]
    exact TerminalGroup.pool_cache_subset data normal original r H group hr0 hH0 out cost c hsound good hparts root a
  rw [TerminalGroup.allocated_exact data normal original r H group hr0 hH0 out cost good hparts hcorrect]
  have hr : Disjoint R (Outer.privateUnion retained) := by
    apply disjoint_iUnion_right.mpr
    intro root
    apply disjoint_iUnion_right.mpr
    intro a
    exact (hd root a).mono_right (hs root a)
  refine ⟨disjoint_union_right.mpr ⟨hr.symm,Outer.retained_private_disjoint _ G retained priv hp hs⟩,?_⟩
  rw [union_left_comm,Outer.private_union_partition _ G retained priv hp hs]

omit hvalid hcorrect in
theorem TerminalGroup.full_cache_correct (R : Set ℝ) (R0 : List (Parent n))
    (hR : CacheValid (measureProfile cost) R R0) (hd : ∀ root a, Disjoint R (G.piece root a)) :
    CacheValid (measureProfile cost)
      (R ∪ Outer.privateUnion (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate))
      (Outer.fullResidueCache R0 (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) := by
  apply Outer.full_residue_cache_correct (measureProfile cost) G
    (TerminalGroup.poolCache data normal original r H group hr0 hH0 out)
    (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
  · intro root a
    rw [hG]
    exact TerminalGroup.pool_private_correct data normal original r H group hr0 hH0 out
      cost c hsound good hparts oldPrivate hold root a
  · exact hR
  · exact hd

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.base_sound
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.domain_partition
