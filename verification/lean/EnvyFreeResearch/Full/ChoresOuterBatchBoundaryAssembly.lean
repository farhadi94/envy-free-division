import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryCache
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryTerminal
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryState
import EnvyFreeResearch.Full.ChoresComponentBoundaryAugment
import EnvyFreeResearch.Full.ChoresOuterResidueAssembly
import EnvyFreeResearch.Full.ChoresTerminalPhysical

/-! Physical allocation and complete-residue assembly preserve the recorded
boundary set; frozen ancestors and zero-cost components are included. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set IntervalOracle InitialPartition OrderedUnion Boundary Scheduler Components
open ChoreComposition SubCorePhysical Suffix
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem pool_allocation_known (points : Set ℝ) (pool : List (Package (Fin n) RootId))
    (cache : RootId → Fin n → List (Parent n)) (hc : ∀ root p, CacheKnown points (cache root p)) :
    AllocationKnown points (poolAllocation pool cache) := by
  intro i
  exact join_labels_known points _ (fun j => hc _ _) _

theorem full_residue_known [Fintype RootId] (points : Set ℝ) (R0 : List (Parent n))
    (privateCache : RootId → Fin n → List (Parent n)) (hR : CacheKnown points R0)
    (hp : ∀ root p, CacheKnown points (privateCache root p)) :
    CacheKnown points (fullResidueCache R0 privateCache) :=
  assemble_known (hR.append (join_labels_known points (fun j : RootId × Fin n => privateCache j.1 j.2)
    (fun j => hp j.1 j.2) Finset.univ.toList))

variable [Fintype RootId] (data : Data n RootId) [Nonempty (Fin data.size)]
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)
    (points : Set ℝ) (hold : DataKnown points original data)
    (hout : RecordedKnown id points out)
include hold

include hout in
theorem terminal_updated_known (root : RootId) (p : Fin n) :
    CacheKnown points (Terminal.updatedCache data original r H A out root p) := by
  unfold Terminal.updatedCache ComponentClosed.patchedCache ComponentPhysical.patchCache
  split
  · unfold ComponentClosed.nextCache ComponentAssignment.dispatch
    split
    · unfold ComponentDonors.affineCache
      apply proposal_cache_known points
      · intro q j parent hp
        exact ((hold.snapshots _).table (q,j)).2 parent (List.mem_append_left _ hp)
      · exact terminal_fronts_known data original r H points hold.snapshots _ _
      · intro parent hp
        exact (hout.2.2.2 _) parent (List.mem_append_left _ hp)
    · intro parent hp
      exact ((hold.snapshots _).table _).2 parent (List.mem_append_left _ hp)
  · exact hold.cache root p

theorem terminal_full_allocation_known (p : Fin n) (t : Reveal.TerminalClass n)
    (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
    (out : ComponentClosed.Result (Root := Fin data.size) t.participants)
    (hout : RecordedKnown id points out) :
    AllocationKnown points (Terminal.fullAllocation data original r H p t hmany out) :=
  pool_allocation_known points _ _
    (terminal_updated_known data original r H t.participants out points hold hout)
end EnvyFreeResearch.Full.Chores.Outer
