import EnvyFreeResearch.Full.ChoresPackageLedger
import EnvyFreeResearch.Full.ChoresAugmentCache

/-! Persistent physical piece caches indexed by immutable original root IDs.
Updating a group's live roots leaves every frozen ancestor untouched; this
is derived from literal root-ID distinctness. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentPhysical
open Set MeasureTheory ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root]
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (hlive : ∀ s, (packages s).live = some (frames s))
  (hdistinct : (Finset.univ.toList.flatMap (fun s => (packages s).ids)).Nodup)

include hlive

theorem live_mem_ids (s : Root) : (frames s).root ∈ (packages s).ids := by
  simp [Package.ids, hlive s]

omit hlive in
theorem frozen_mem_ids (s : Root) (a : Allocation (Fin n) RootId) (ha : a ∈ (packages s).frozen) :
    a.root ∈ (packages s).ids :=
  List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

include hdistinct

theorem package_ids_disjoint (s t : Root) (hst : s ≠ t) :
    List.Disjoint (packages s).ids (packages t).ids := by
  have hp := (List.nodup_flatMap.mp hdistinct).2
  have hr : Finset.univ.toList.Pairwise
      (fun s t : Root => s ≠ t → List.Disjoint (packages s).ids (packages t).ids) :=
    hp.imp (fun {s t} (h : List.Disjoint (packages s).ids (packages t).ids) (_ : s ≠ t) => h)
  have hf : Finset.univ.toList.Pairwise
      (fun s t : Root => t ≠ s → List.Disjoint (packages t).ids (packages s).ids) :=
    hp.imp (fun h _ => h.symm)
  exact List.Pairwise.forall_of_forall_of_flip (fun _ _ h => (h rfl).elim) hr hf
    (by simp) (by simp) hst

theorem live_roots_injective : Function.Injective (fun s => (frames s).root) := by
  intro s t h
  change (frames s).root = (frames t).root at h
  by_contra hst
  have hd := package_ids_disjoint packages frames hlive hdistinct s t hst
  exact List.disjoint_left.mp hd (live_mem_ids packages frames hlive s)
    (by rw [h]; exact live_mem_ids packages frames hlive t)

theorem frozen_root_not_live (s t : Root) (a : Allocation (Fin n) RootId)
    (ha : a ∈ (packages s).frozen) : a.root ≠ (frames t).root := by
  by_cases hst : s = t
  · subst t
    have hnd : (packages s).ids.Nodup := (List.nodup_flatMap.mp hdistinct).1 s (by simp)
    have hd := List.Nodup.disjoint hnd
    intro heq
    apply List.disjoint_left.mp hd (List.mem_map.mpr ⟨a, ha, rfl⟩)
    simp [hlive s, heq]
  · intro heq
    have hd := package_ids_disjoint packages frames hlive hdistinct s t hst
    exact List.disjoint_left.mp hd (frozen_mem_ids packages s a ha)
      (heq ▸ live_mem_ids packages frames hlive t)

omit hlive hdistinct

def patchCache (old : RootId → Fin n → List (Parent n))
    (next : Root → Fin n → List (Parent n)) (r : RootId) (p : Fin n) : List (Parent n) :=
  if h : ∃ s, (frames s).root = r then next h.choose p else old r p

theorem patch_live (old : RootId → Fin n → List (Parent n))
    (next : Root → Fin n → List (Parent n))
    (hinj : Function.Injective (fun s => (frames s).root)) (s : Root) (p : Fin n) :
    patchCache frames old next (frames s).root p = next s p := by
  have h : ∃ t, (frames t).root = (frames s).root := ⟨s, rfl⟩
  rw [patchCache, dite_eq_left h, hinj h.choose_spec]

theorem patch_other (old : RootId → Fin n → List (Parent n))
    (next : Root → Fin n → List (Parent n)) (r : RootId)
    (hother : ∀ s, (frames s).root ≠ r) (p : Fin n) :
    patchCache frames old next r p = old r p := by
  rw [patchCache, dite_eq_right (by simpa only [not_exists] using hother)]

theorem patch_valid (P : Profile (Fin n)) (old : RootId → Fin n → List (Parent n))
    (next : Root → Fin n → List (Parent n))
    (hold : ∀ r p, Valid P (old r p) ∧ Ordered (old r p))
    (hnext : ∀ s p, Valid P (next s p) ∧ Ordered (next s p)) (r : RootId) (p : Fin n) :
    Valid P (patchCache frames old next r p) ∧ Ordered (patchCache frames old next r p) := by
  unfold patchCache
  split
  · exact hnext _ _
  · exact hold _ _

theorem patch_subset (G : PackageGeometry.Pieces RootId (Fin n))
    (old : RootId → Fin n → List (Parent n)) (next : Root → Fin n → List (Parent n))
    (hold : ∀ r p, material (old r p) ⊆ G.piece r p)
    (hnext : ∀ s p, material (next s p) ⊆ G.piece (frames s).root p) (r : RootId) (p : Fin n) :
    material (patchCache frames old next r p) ⊆ G.piece r p := by
  unfold patchCache
  split
  next h =>
    intro x hx
    have hh := hnext h.choose p hx
    simpa only [h.choose_spec] using hh
  next _ => exact hold _ _

def cachedPieces (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p) :
    PackageGeometry.Pieces RootId (Fin n) :=
  G.retained (fun r p => material (cache r p)) hsub (fun _ _ => material_measurable _)

theorem patch_realizes (cost : Fin n → Measure ℝ)
    (old : RootId → Fin n → List (Parent n)) (next : Root → Fin n → List (Parent n))
    (nextAllocation : Root → Allocation (Fin n) RootId)
    (hinj : Function.Injective (fun s => (frames s).root))
    (havoid : ∀ s t a, a ∈ (packages s).frozen → a.root ≠ (frames t).root)
    (hroot : ∀ s, (nextAllocation s).root = (frames s).root)
    (hold : ∀ s a, a ∈ (packages s).frozen → ∀ i p,
      a.cost i p = (cost i).real (material (old a.root p)))
    (hnext : ∀ s i p, (nextAllocation s).cost i p = (cost i).real (material (next s p)))
    (allocations : List (Allocation (Fin n) RootId))
    (hallocations : ∀ a ∈ allocations,
      (∃ s, a ∈ (packages s).frozen) ∨ ∃ s, a = nextAllocation s) :
    ∀ a ∈ allocations, ∀ i p,
      a.cost i p = (cost i).real (material (patchCache frames old next a.root p)) := by
  intro a ha i p
  rcases hallocations a ha with ⟨s, hs⟩ | ⟨s, rfl⟩
  · rw [patch_other frames old next a.root (fun t => (havoid s t a hs).symm) p]
    exact hold s a hs i p
  · rw [hroot s, patch_live frames old next hinj s p]
    exact hnext s i p

end EnvyFreeResearch.Full.Chores.ComponentPhysical
