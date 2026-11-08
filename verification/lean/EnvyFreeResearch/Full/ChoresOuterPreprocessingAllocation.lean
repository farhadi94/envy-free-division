import EnvyFreeResearch.Full.ChoresClearanceAllocation
import EnvyFreeResearch.Full.ChoresCompletionZero

/-! Query-free allocation of all clearance snapshots, including their
zero-cost material. Their fixed bundles are kept outside the mutable pool. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot Completion
open scoped Classical
variable {n : ℕ}

def snapshotAllocation (out : Snapshot.Output n) : Completion.Allocation n (Fin n) := ⟨out.parents⟩
def batchAllocation : List (Snapshot.Output n) → Completion.Allocation n (Fin n)
  | [] => ⟨fun _ => []⟩
  | out::rest => (snapshotAllocation out).join (batchAllocation rest)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem snapshot_allocation_sound {U : Set ℝ} {c : Fin n} {out : Snapshot.Output n}
    (h : Snapshot.Sound cost U c out) :
    (snapshotAllocation out).Sound cost id out.carrier := by
  constructor
  · intro i
    exact ⟨(h.parent_cache i).1,(h.parent_cache i).2.1,rfl⟩
  · exact h.pieces_disjoint
  · rfl
  · exact h.envy_free

theorem batch_allocation_sound {U : Set ℝ} {xs : List (Snapshot.Output n)}
    {cache : List (Parent n)} (chain : Snapshot.AnyChain cost U xs cache) :
    (batchAllocation xs).Sound cost id (batchMaterial xs) := by
  induction chain with
  | nil U cache hc =>
    constructor
    · intro i
      simp [batchAllocation,CacheValid,Valid,Ordered,material]
    · intro i j hij
      simp [batchAllocation,material]
    · simp [batchAllocation,batchMaterial,material]
    · intro i j
      simp [batchAllocation,material]
  | @cons U first rest cache c hs chain ih =>
    have hd : Disjoint first.carrier (batchMaterial rest) := by
      apply hs.carrier_residue_disjoint.mono_right
      rw [hs.residue_eq]
      exact batch_material_subset rest _ chain.subsets.1
    exact Allocation.join_sound cost id first.carrier (batchMaterial rest)
      (snapshotAllocation first) (batchAllocation rest) (snapshot_allocation_sound cost hs) ih hd

theorem batch_zero_complete {U : Set ℝ} {xs : List (Snapshot.Output n)}
    {cache : List (Parent n)} (chain : Snapshot.AnyChain cost U xs cache)
    (z : Fin n) (hz : (cost z).real (material cache)=0) :
    ((batchAllocation xs).join (zeroAllocation z cache)).Sound cost id U := by
  rw [← chain.cover]
  exact zero_complete cost id (batchMaterial xs) (material cache) (batchAllocation xs)
    (batch_allocation_sound cost chain) cache chain.final_cache chain.final_residue_disjoint z hz
end EnvyFreeResearch.Full.Chores.Outer
