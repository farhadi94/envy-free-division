import EnvyFreeResearch.Full.ChoresOuterPreprocessingAllocation
import EnvyFreeResearch.Full.ChoresOuterEntrance

/-! The fixed clearance allocation is disjoint from the entire mutable
original pool and the final residue, and is retained on every exit. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot Completion
open scoped Classical
variable {n : ℕ}

def preprocessingDomain (out : Preprocessing.Output n) : Set ℝ :=
  batchMaterial out.originals ∪ material out.residue

def preprocessingFixed (out : Preprocessing.Output n) : Completion.Allocation n (Fin n) :=
  batchAllocation out.clearance

theorem batch_member_subset (xs : List (Snapshot.Output n)) (item : Snapshot.Output n)
    (hm : item ∈ xs) : item.carrier ⊆ batchMaterial xs := by
  induction xs with
  | nil => cases hm
  | cons first rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact subset_union_left
    · exact (ih hm).trans subset_union_right

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} (out : Preprocessing.Output n)
  (horiginal : Chain cost c U out.originals out.middle)
  (hclear : AnyChain cost (material out.middle) out.clearance out.residue)
include horiginal hclear

theorem preprocessing_partition :
    batchMaterial out.clearance ∪ preprocessingDomain out=U := by
  rw [preprocessingDomain,← horiginal.cover,← hclear.cover]
  ac_rfl

theorem preprocessing_disjoint :
    Disjoint (batchMaterial out.clearance) (preprocessingDomain out) := by
  apply disjoint_union_right.mpr
  exact ⟨horiginal.final_residue_disjoint.symm.mono_left
    (batch_material_subset _ _ hclear.subsets.1), hclear.final_residue_disjoint⟩

omit horiginal in
theorem preprocessing_fixed_sound :
    (preprocessingFixed out).Sound cost id (batchMaterial out.clearance) :=
  batch_allocation_sound cost hclear

theorem preprocessing_attach_sound (inner : Completion.Allocation n (Fin n))
    (hinner : inner.Sound cost id (preprocessingDomain out)) :
    ((preprocessingFixed out).join inner).Sound cost id U := by
  rw [← preprocessing_partition cost out horiginal hclear]
  exact Allocation.join_sound cost id _ _ _ _ (preprocessing_fixed_sound cost out hclear)
    hinner (preprocessing_disjoint cost out horiginal hclear)

theorem preprocessing_zero_sound (z : Fin n)
    (hz : (cost z).real (material out.residue)=0) :
    ((batchAllocation (out.originals++out.clearance)).join (zeroAllocation z out.residue)).Sound cost id U :=
  batch_zero_complete cost (horiginal.any.append hclear) z hz

theorem preprocessing_original_residue_disjoint (s : Fin out.originals.length) (p : Fin n) :
    Disjoint ((out.originals.get s).piece p) (material out.residue) := by
  have hor : (out.originals.get s).piece p ⊆ batchMaterial out.originals := by
    apply (subset_iUnion (fun p => (out.originals.get s).piece p) p).trans
    exact batch_member_subset _ _ (List.get_mem _ _)
  exact horiginal.final_residue_disjoint.mono hor hclear.subsets.2
end EnvyFreeResearch.Full.Chores.Outer
