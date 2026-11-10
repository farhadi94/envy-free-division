import EnvyFreeResearch.Full.RefinedChoresTerminalCohortCaches
import EnvyFreeResearch.Full.RefinedChoresTerminalAggregatePool

/-! The concrete closed pool after a selected terminal affine cohort.
All original IDs, untouched packages, and frozen ancestors are retained. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches RefinedChoresTerminalAggregate
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)

def TerminalGroup.pool := terminalPool data group.roots
  (TerminalGroup.output data normal original r H group hr0 hH0 out)

def TerminalGroup.poolCache := patchedCache data group.roots
  (TerminalGroup.next data normal original r H group hr0 hH0 out)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include good

theorem TerminalGroup.pool_valid
    (hv : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid) :
    PoolValid (TerminalGroup.pool data normal original r H group hr0 hH0 out) :=
  terminal_pool_valid data group.roots original cost r H good _ hv

theorem TerminalGroup.pool_closed :
    ∀ package ∈ TerminalGroup.pool data normal original r H group hr0 hH0 out, package.live = none :=
  terminal_pool_closed data group.roots original cost r H good _ rfl

include hparts

theorem TerminalGroup.pool_ids
    (hc : PhysicalCorrect (affineUtility cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation) :
    ((TerminalGroup.pool data normal original r H group hr0 hH0 out).flatMap Package.ids).Perm Finset.univ.toList := by
  apply closed_pool_ids data group.roots original cost r H good group.terminalClass.participants group.label
    (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out (by simp [TerminalGroup.Root])
  · simp [TerminalGroup.Root]
  · apply donations_wellFormed group.terminalClass.participants group.label
      (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
      (data.packages ∘ group.roots) (TerminalGroup.gaps data normal original r H group) out
      cost (TerminalGroup.blocks data normal original r H group) hparts hc
    · intro s
      exact good.live _
    · intro s
      exact (active_package_valid data original cost r H good _).live_good _ (good.live _)
    · intro s a
      exact ((data.tracked (group.roots s)).exact a a).mpr (RefinedChoresPartialGraph.allowed_refl _ _ a)

include hsound

theorem TerminalGroup.pool_cache_valid (root : RootId) (a : Fin n) :
    Valid (measureProfile cost) (TerminalGroup.poolCache data normal original r H group hr0 hH0 out root a) ∧
      Ordered (TerminalGroup.poolCache data normal original r H group hr0 hH0 out root a) :=
  patched_valid data original cost r H good group.roots _
    (TerminalGroup.next_valid data normal original r H group hr0 hH0 cost c hsound out hparts) root a

theorem TerminalGroup.pool_cache_subset (root : RootId) (a : Fin n) :
    material (TerminalGroup.poolCache data normal original r H group hr0 hH0 out root a) ⊆ (original root).piece a :=
  patched_subset data original cost r H good group.roots _
    (TerminalGroup.next_subset data normal original r H group hr0 hH0 cost c hsound out hparts) root a

theorem TerminalGroup.pool_realizes :
    ∀ allocation ∈ (TerminalGroup.pool data normal original r H group hr0 hH0 out).flatMap Package.allocations,
      ∀ i a, allocation.cost i a = (cost i).real
        (material (TerminalGroup.poolCache data normal original r H group hr0 hH0 out allocation.root a)) :=
  closed_pool_realizes data group.roots original cost r H good group.terminalClass.participants group.label
    (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out (by simp [TerminalGroup.Root])
    (TerminalGroup.next data normal original r H group hr0 hH0 out)
    (TerminalGroup.next_cost data normal original r H group hr0 hH0 cost c hsound good out hparts)

omit hsound hparts good in
theorem TerminalGroup.donor_mem (j : group.terminalClass.participants) :
    actualDonor group.terminalClass.participants group.label (data.frames ∘ group.roots)
      (TerminalGroup.path data normal original r H group hr0 hH0)
      (TerminalGroup.gaps data normal original r H group) out j ∈
      (TerminalGroup.pool data normal original r H group hr0 hH0 out).flatMap Package.allocations := by
  apply List.mem_flatMap.mpr
  refine ⟨TerminalGroup.output data normal original r H group hr0 hH0 out,?_,?_⟩
  · exact List.mem_append_right _ List.mem_cons_self
  · exact actual_donor_member group.terminalClass.participants group.label (data.frames ∘ group.roots)
      (TerminalGroup.path data normal original r H group hr0 hH0) (data.packages ∘ group.roots)
      (TerminalGroup.gaps data normal original r H group) out (by simp [TerminalGroup.Root]) j

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.pool_ids
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.pool_realizes
