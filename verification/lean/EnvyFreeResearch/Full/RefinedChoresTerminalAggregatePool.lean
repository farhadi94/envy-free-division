import EnvyFreeResearch.Full.RefinedChoresTerminalAggregateIds
import EnvyFreeResearch.Full.RefinedChoresDataPatch
import EnvyFreeResearch.Full.RefinedChoresCohort
import EnvyFreeResearch.Full.ChoresOuterFiltering

/-! The literal terminal pool closes all unselected active packages and
retains all previously frozen packages. Original IDs and physical caches
are preserved by a single cohort replacement. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
open Set MeasureTheory IntervalOracle ChoreComposition
open Chores Chores.InitialPartition Chores.OrderedUnion
open RefinedChoresData
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Fintype RootId]
    (data : Data n RootId) (roots : Root ↪ Fin data.size)

def terminalPool (output : Package (Fin n) RootId) : List (Package (Fin n) RootId) :=
  data.closed ++ (output :: (remainingRoots data roots).map (fun s => (data.packages s).close))

variable (original : RootId → Snapshot.Output n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
    (output : Package (Fin n) RootId)
include good

theorem terminal_pool_valid (houtput : output.Valid) : PoolValid (terminalPool data roots output) := by
  intro package hp
  rcases List.mem_append.mp hp with hp | hp
  · exact good.package_valid _ (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact houtput
    · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
      exact package_close_valid _ (good.package_valid _
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩)))

theorem terminal_pool_ids
    (houtput : output.ids.Perm (Finset.univ.toList.flatMap (fun s => (data.packages (roots s)).ids))) :
    ((terminalPool data roots output).flatMap Package.ids).Perm Finset.univ.toList := by
  have h := (closed_replacement_ids data roots output houtput).append_left
    (data.closed.flatMap Package.ids)
  have hp : ((terminalPool data roots output).flatMap Package.ids).Perm
      (data.allPackages.flatMap Package.ids) := by
    simpa only [terminalPool,List.flatMap_append,Data.allPackages] using h
  exact hp.trans good.all_ids

theorem terminal_pool_closed (hout : output.live=none) :
    ∀ package ∈ terminalPool data roots output, package.live=none := by
  intro package hp
  rcases List.mem_append.mp hp with hp | hp
  · exact good.closed package hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact hout
    · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
      exact package_close_live _

variable (nextAllocation : Root → ChoreComposition.Allocation (Fin n) RootId)
    (hout : ∀ a ∈ output.allocations,
      (∃ s : Root, a ∈ (data.packages (roots s)).frozen) ∨ ∃ s, a=nextAllocation s)
include hout

theorem terminal_pool_origin (a : ChoreComposition.Allocation (Fin n) RootId)
    (ha : a ∈ (terminalPool data roots output).flatMap Package.allocations) :
    AllocationOrigin data roots nextAllocation a := by
  obtain ⟨package,hpackage,halloc⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp hpackage with hpackage | hpackage
  · exact Or.inl (List.mem_flatMap.mpr ⟨package,hpackage,halloc⟩)
  · rcases List.mem_cons.mp hpackage with rfl | hpackage
    · rcases hout a halloc with ⟨s,hs⟩ | ⟨s,hs⟩
      · exact Or.inr (Or.inl ⟨roots s,hs⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨s,hs⟩))
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hpackage
      rw [Outer.package_close_allocations] at halloc
      have hsn : s ∉ Set.range roots := (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
      simp only [Package.allocations,good.live s,Option.toList_some,List.map_cons,List.map_nil,
        List.mem_append,List.mem_singleton] at halloc
      rcases halloc with ha | ha
      · exact Or.inr (Or.inl ⟨s,ha⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨s,hsn,ha⟩))

theorem terminal_pool_realizes (next : Root → Fin n → List (Parent n))
    (hroot : ∀ s, (nextAllocation s).root=data.source (roots s))
    (hcost : ∀ s i p, (nextAllocation s).cost i p=(cost i).real (material (next s p))) :
    ∀ a ∈ (terminalPool data roots output).flatMap Package.allocations, ∀ i p,
      a.cost i p=(cost i).real (material (patchedCache data roots next a.root p)) :=
  patched_realizes data original cost r H good roots next nextAllocation hroot hcost _
    (terminal_pool_origin data roots original cost r H good output nextAllocation hout)

section ClosedBatch
variable [Nonempty Root]
    (A : Finset (Fin n)) (p : Fin n)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen
      (fun a b => b ∈ (data.frames (roots s)).allowed a) j p)
    (gap : Root → Fin n → Fin n → ℝ)
    (out : RefinedChoresClosed.Result (Root := Root) A)
    (hmany : Fintype.card A < Fintype.card Root)
omit hout in
def closedTerminalPool := terminalPool data roots
  (RefinedChoresClosed.outputPackage A p (data.frames ∘ roots) hpath (data.packages ∘ roots) gap out hmany)

omit hout in
theorem closed_pool_ids (hcard : Fintype.card Root=Fintype.card A+1)
    (hwell : ∀ d ∈ RefinedChoresClosed.donations A p (data.frames ∘ roots) hpath
      (data.packages ∘ roots) gap out, d.WellFormed) :
    ((closedTerminalPool data roots A p hpath gap out hmany).flatMap Package.ids).Perm Finset.univ.toList := by
  apply terminal_pool_ids data roots original cost r H good
  exact output_ids A p (data.frames ∘ roots) hpath (data.packages ∘ roots) gap out hmany hcard hwell

omit hout in
theorem closed_pool_origin (a : ChoreComposition.Allocation (Fin n) RootId)
    (ha : a ∈ (closedTerminalPool data roots A p hpath gap out hmany).flatMap Package.allocations) :
    AllocationOrigin data roots (RefinedChoresClosedCaches.nextAllocation A p (data.frames ∘ roots) hpath gap out) a := by
  apply terminal_pool_origin data roots original cost r H good _ _ _ a ha
  intro a ha
  exact output_allocation_member A p (data.frames ∘ roots) hpath (data.packages ∘ roots) gap out hmany
    (fun s => good.live (roots s)) a ha

omit hout in
theorem closed_pool_realizes (next : Root → Fin n → List (Parent n))
    (hnext : ∀ s i q, (RefinedChoresClosedCaches.nextAllocation A p (data.frames ∘ roots) hpath gap out s).cost i q =
      (cost i).real (material (next s q))) :
    ∀ a ∈ (closedTerminalPool data roots A p hpath gap out hmany).flatMap Package.allocations, ∀ i q,
      a.cost i q = (cost i).real (material (patchedCache data roots next a.root q)) := by
  apply patched_realizes data original cost r H good roots next
    (RefinedChoresClosedCaches.nextAllocation A p (data.frames ∘ roots) hpath gap out)
  · intro s
    exact (RefinedChoresClosedCaches.next_allocation_root A p (data.frames ∘ roots) hpath gap out s).trans
      (good.source (roots s))
  · exact hnext
  · exact closed_pool_origin data roots original cost r H good A p hpath gap out hmany
end ClosedBatch

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
#print axioms EnvyFreeResearch.Full.RefinedChoresTerminalAggregate.closed_pool_ids
#print axioms EnvyFreeResearch.Full.RefinedChoresTerminalAggregate.closed_pool_realizes
