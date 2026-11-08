import EnvyFreeResearch.Full.ChoresOuterPackageFacts

/-! The initial committed state is constructed from the recorded original
snapshots. Every physical and finite scheduler invariant follows directly
from those snapshots; no successful later step is assumed. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler ChoreComposition
open scoped Classical

variable {n J : ℕ}

def initialData (original : Fin J → Snapshot.Output n) : Data n (Fin J) where
  size := J
  source := id
  pending := PendingState.initial
  visited := Visited.initial
  packages s := Package.seed (PackageGeometry.initialFrame s (original s).parents (original s).equalizers)
  frames s := PackageGeometry.initialFrame s (original s).parents (original s).equalizers
  frontier _ p := p
  cache s := (original s).parents
  closed := []

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (original : Fin J → Snapshot.Output n) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (r : Fin n → ℝ) (H : ℝ) (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)

include hsound hr hH

theorem initial_good : (initialData original).Good original cost r H := by
  have hinitial (s : Fin J) :
      (Package.seed (PackageGeometry.initialFrame s (original s).parents (original s).equalizers)).Valid ∧
      (∀ i p, (PackageGeometry.initialFrame s (original s).parents (original s).equalizers).allocation.cost i p=
        (cost i).real ((original s).piece p)) := by
    obtain ⟨U,hs⟩ := hsound s
    exact PackageGeometry.recorded_initial_package cost s (original s).piece (original s).parents
      (snapshot_parent_cache hs) hs.envy_free (original s).equalizers (snapshot_equalizers hs)
      (fun p => (hs.own_equalizers p).1)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro package hp
    change package ∈ []++List.ofFn (fun s => Package.seed
      (PackageGeometry.initialFrame s (original s).parents (original s).equalizers)) at hp
    rw [List.nil_append] at hp
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hp
    exact (hinitial s).1
  · have hperm : (List.finRange J).Perm (Finset.univ.toList : List (Fin J)) := by
      apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr
      intro s
      simp
    simpa [Data.allPackages,initialData,Package.ids,Package.seed,PackageGeometry.initialFrame,
      List.ofFn_eq_map,List.flatMap_map] using hperm
  · intro package hp
    cases hp
  · exact fun _ => rfl
  · exact fun _ => rfl
  · exact fun s => initial_original s (original s)
  · intro root p
    obtain ⟨U,hs⟩ := hsound root
    exact ⟨(hs.parent_cache p).1,(hs.parent_cache p).2.1⟩
  · exact fun _ _ => Subset.rfl
  · intro a ha i p
    obtain ⟨package,hp,ha⟩ := List.mem_flatMap.mp ha
    change package ∈ []++List.ofFn (fun s => Package.seed
      (PackageGeometry.initialFrame s (original s).parents (original s).equalizers)) at hp
    rw [List.nil_append] at hp
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hp
    simp only [Package.allocations,Package.seed,List.nil_append,Option.toList_some,
      List.map_cons,List.map_nil,List.mem_singleton] at ha
    subst a
    exact (hinitial s).2 i p
  · intro s p
    obtain ⟨U,hs⟩ := hsound s
    exact (hs.own_equalizers p).1.symm
  · intro s p i
    simp only [initialData,PackageGeometry.initialFrame,Visited.initial,Components.Edge,
      List.mem_singleton,Equiv.Perm.one_apply,Finset.mem_singleton]
    constructor
    · intro h
      exact ⟨1,rfl,h.symm⟩
    · rintro ⟨σ,rfl,h⟩
      exact h.symm
  · intro s p
    have hinv := Frontier.initial_invariant (weight (original s).equalizers p)
      (rankOf (original s).equalizers p) r H p (rank_owner _ _) (rank_le _ _) (hr p) hH
    have hc : (initialData original).component p={p} := by
      ext i
      simp only [Data.component,initialData,PendingState.initial,Partition.initial,
        Partition.mem_component,Finset.mem_singleton,id_eq]
    change Frontier.Invariant _ _ _ _ _ ((initialData original).component p) {p} ∅ p
    rw [hc]
    exact hinv
  · intro s i p
    obtain ⟨U,hs⟩ := hsound s
    have hv := original_equalizer_value cost hs (PackageGeometry.initialFrame s
      (original s).parents (original s).equalizers) (initial_original s (original s)) i p p
    rw [(hs.own_equalizers p).1,material_value cost _ (hs.parent_cache p).1
      (hs.parent_cache p).2.1] at hv
    change baselines (original s).parents i-cachedValue ((original s).parents p) i=
      baselines (original s).parents i-((original s).equalizers (p,p)).values i
    rw [← hv]
    rfl
  · intro p proposed hp
    cases hp
  · intro root p i
    change (cost i).real ((original root).piece p \ (original root).piece p) ≤ _
    rw [Set.sdiff_self,measureReal_empty]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hr i)) hH.le

end EnvyFreeResearch.Full.Chores.Outer
