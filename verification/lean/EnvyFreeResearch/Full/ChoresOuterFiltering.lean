import EnvyFreeResearch.Full.ChoresOuterPool

/-! Filtering an old live pool closes every rejected package unchanged.
The actual selected list and rejected list partition the old inputs, and
closure preserves the literal allocation records and every original ID. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open ChoreComposition
open scoped Classical

variable {n : ℕ} {Root RootId : Type*}

def rejected (old kept : List Root) : List Root := old.filter (fun s => decide (s ∉ kept))

theorem mem_rejected (old kept : List Root) (s : Root) :
    s ∈ rejected old kept ↔ s ∈ old ∧ s ∉ kept := by simp [rejected]

theorem rejected_kept_perm (old kept : List Root) (hold : old.Nodup) (hkept : kept.Nodup)
    (hsub : kept ⊆ old) : (rejected old kept++kept).Perm old := by
  have hd : List.Disjoint (rejected old kept) kept := by
    apply List.disjoint_left.mpr
    intro s hs hk
    exact ((mem_rejected old kept s).mp hs).2 hk
  have hnd : (rejected old kept++kept).Nodup := (hold.filter _).append hkept hd
  apply (List.perm_ext_iff_of_nodup hnd hold).mpr
  intro s
  rw [List.mem_append,mem_rejected]
  constructor
  · rintro (hs | hs)
    · exact hs.1
    · exact hsub hs
  · intro hs
    by_cases hk : s ∈ kept
    · exact Or.inr hk
    · exact Or.inl ⟨hs,hk⟩

theorem package_close_allocations (package : Package (Fin n) RootId) :
    package.close.allocations=package.allocations := by
  cases hs : package.live <;> simp [Package.close,Package.allocations,hs]

def filteredPool (old kept : List Root) (packages : Root → Package (Fin n) RootId)
    (closed : List (Package (Fin n) RootId)) : List (Package (Fin n) RootId) :=
  (closed++(rejected old kept).map (fun s => (packages s).close))++kept.map packages

theorem filtered_allocations_perm (old kept : List Root) (hold : old.Nodup) (hkept : kept.Nodup)
    (hsub : kept ⊆ old) (packages : Root → Package (Fin n) RootId)
    (closed : List (Package (Fin n) RootId)) :
    (filteredPool old kept packages closed).flatMap Package.allocations |>.Perm
      ((closed++old.map packages).flatMap Package.allocations) := by
  have h := (rejected_kept_perm old kept hold hkept hsub).flatMap_right
    (fun s => (packages s).allocations)
  simpa only [filteredPool,List.flatMap_append,List.flatMap_map,Function.comp_def,
    package_close_allocations,List.append_assoc] using h.append_left (closed.flatMap Package.allocations)

theorem filtered_ids_perm (old kept : List Root) (hold : old.Nodup) (hkept : kept.Nodup)
    (hsub : kept ⊆ old) (packages : Root → Package (Fin n) RootId)
    (closed : List (Package (Fin n) RootId)) :
    ((filteredPool old kept packages closed).flatMap Package.ids).Perm
      ((closed++old.map packages).flatMap Package.ids) := by
  have h := (filtered_allocations_perm old kept hold hkept hsub packages closed).map
    ChoreComposition.Allocation.root
  simpa only [PackageGeometry.pool_allocation_roots] using h

theorem filtered_valid (old kept : List Root) (hsub : kept ⊆ old)
    (packages : Root → Package (Fin n) RootId) (closed : List (Package (Fin n) RootId))
    (hc : PoolValid closed) (hp : ∀ s ∈ old, (packages s).Valid) :
    PoolValid (filteredPool old kept packages closed) := by
  intro package hpackage
  obtain hpackage | hpackage := List.mem_append.mp hpackage
  · obtain hpackage | hpackage := List.mem_append.mp hpackage
    · exact hc package hpackage
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hpackage
      exact package_close_valid _ (hp s ((mem_rejected old kept s).mp hs).1)
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hpackage
    exact hp s (hsub hs)

end EnvyFreeResearch.Full.Chores.Outer
