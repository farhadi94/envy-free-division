import EnvyFreeResearch.Full.ChoresComponentBoundaryUnion
import EnvyFreeResearch.Full.ChoresComponentDomination
import EnvyFreeResearch.Full.ChoresCompletionFinish

/-! Pure physical assembly preserves endpoint provenance. Sorting and dropping
literally empty components cannot create a new boundary. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n k : ℕ} {Agent : Type*}

theorem assemble_known {points : Set ℝ} {parts : List (Parent n)} (h : CacheKnown points parts) :
    CacheKnown points (Augment.assemble parts) := by
  intro p hp
  have hf : p ∈ Augment.positiveComponents parts := (List.mergeSort_perm _ _).mem_iff.mp hp
  exact h p (List.mem_filter.mp hf).1

def AllocationKnown (points : Set ℝ) (out : Completion.Allocation n Agent) : Prop :=
  ∀ i, CacheKnown points (out.pieces i)

theorem AllocationKnown.mono {old more : Set ℝ} {out : Completion.Allocation n Agent}
    (h : AllocationKnown old out) (hm : old ⊆ more) : AllocationKnown more out :=
  fun i => (h i).mono hm

theorem join_known {points : Set ℝ} {first second : Completion.Allocation n Agent}
    (hf : AllocationKnown points first) (hs : AllocationKnown points second) :
    AllocationKnown points (first.join second) :=
  fun i => assemble_known ((hf i).append (hs i))

theorem reindex_known {A B : Type*} {points : Set ℝ} {out : Completion.Allocation n A}
    (h : AllocationKnown points out) (f : B → A) : AllocationKnown points (out.reindex f) :=
  fun i => h (f i)

theorem extend_known (points : Set ℝ) (agent : Fin k ↪ Fin n) (child : Completion.Allocation n (Fin k))
    (h : AllocationKnown points child) : AllocationKnown points (Population.extend agent child) := by
  intro i
  by_cases hi : i ∈ Set.range agent
  · obtain ⟨a, rfl⟩ := hi
    rw [Population.extend_at]
    exact h a
  · rw [Population.extend_outside agent child i hi]
    simp [CacheKnown]

theorem domination_known (points : Set ℝ) (base : Completion.Allocation n (Fin n))
    (agent : Fin k ↪ Fin n) (child : Completion.Allocation n (Fin k))
    (hb : AllocationKnown points base) (hc : AllocationKnown points child) :
    AllocationKnown points (Population.finishDomination base agent child) :=
  join_known hb (extend_known points agent child hc)

theorem zero_allocation_known (points : Set ℝ) (z : Agent) (cache : List (Parent n))
    (h : CacheKnown points cache) : AllocationKnown points (Completion.zeroAllocation z cache) := by
  intro i
  by_cases hi : i = z
  · simpa only [zeroAllocation, ite_eq_left hi] using h
  · simp [zeroAllocation, hi, CacheKnown]

end EnvyFreeResearch.Full.Chores.Boundary
