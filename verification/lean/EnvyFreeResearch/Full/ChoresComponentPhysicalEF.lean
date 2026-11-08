import EnvyFreeResearch.Full.ChoresComponentRealization
import EnvyFreeResearch.Full.ChoresAugmentComplement

/-! Package reserve validity yields physical envy-freeness for the actual
finite-union caches, including every frozen ancestor and the live root. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentPhysical
open Set MeasureTheory ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {RootId : Type*}

private theorem valid_classical (package : Package (Fin n) RootId) (h : package.Valid) :
    @Package.Valid (Fin n) RootId (fun a b => Classical.propDecidable (a = b)) package := by
  have heq : (instDecidableEqFin n) = (fun a b : Fin n => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [← heq]
  exact h

def bundle (package : Package (Fin n) RootId) (cache : RootId → Fin n → List (Parent n))
    (i : Fin n) : Set ℝ :=
  ⋃ r : Fin package.allocations.length,
    material (cache (package.allocations.get r).root ((package.allocations.get r).owner.symm i))

def bundleCache (package : Package (Fin n) RootId) (cache : RootId → Fin n → List (Parent n))
    (i : Fin n) : List (Parent n) :=
  Augment.joinLabels (fun r : Fin package.allocations.length =>
    cache (package.allocations.get r).root ((package.allocations.get r).owner.symm i)) Finset.univ.toList

theorem bundle_cache_correct (package : Package (Fin n) RootId) (hd : package.ids.Nodup)
    (G : PackageGeometry.Pieces RootId (Fin n)) (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p)
    (P : Profile (Fin n)) (hv : ∀ r p, Valid P (cache r p) ∧ Ordered (cache r p)) (i : Fin n) :
    CacheValid P (bundle package cache i) (bundleCache package cache i) := by
  have hroots : (package.allocations.map Allocation.root).Nodup := by
    rw [PackageGeometry.allocation_roots]
    exact hd
  have hinj := PackageGeometry.list_roots_injective package.allocations hroots
  let pieces := fun r : Fin package.allocations.length =>
    cache (package.allocations.get r).root ((package.allocations.get r).owner.symm i)
  have hf : Augment.FamilyValid P pieces := by
    refine ⟨fun r => hv _ _, ?_⟩
    intro r t hrt
    exact (@G.disjoint ((package.allocations.get r).root,
      (package.allocations.get r).owner.symm i)
      ((package.allocations.get t).root, (package.allocations.get t).owner.symm i)
      (fun heq => hrt (hinj (congrArg Prod.fst heq)))).mono (hsub _ _) (hsub _ _)
  obtain ⟨hvalid, horder, hm⟩ := Augment.join_labels_valid P pieces hf
    Finset.univ.toList (Finset.nodup_toList _)
  exact ⟨hvalid, horder, by simpa only [bundleCache, bundle, pieces, Finset.mem_toList,
    Finset.mem_univ, iUnion_true] using hm⟩

theorem bundle_envy_free (package : Package (Fin n) RootId) (hv : package.Valid)
    (hd : package.ids.Nodup) (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (hcost : ∀ a ∈ package.allocations, ∀ i p,
      a.cost i p = (cost i).real (material (cache a.root p))) :
    ∀ i j, (cost i).real (bundle package cache i) ≤ (cost i).real (bundle package cache j) := by
  have hroots : (package.allocations.map Allocation.root).Nodup := by
    rw [PackageGeometry.allocation_roots]
    exact hd
  have hc : ∀ a ∈ package.allocations, ∀ i p,
      a.cost i p = (cost i).real ((cachedPieces G cache hsub).piece a.root p) := hcost
  apply (PackageGeometry.indexedPieces (cachedPieces G cache hsub) package.allocations hroots).envy_free
    (PackageGeometry.indexedOwner _) cost (PackageGeometry.indexedBaseline _)
  intro i j hij p
  simp only [PackageGeometry.indexed_debit _ _ _ cost hc, PackageGeometry.indexed_credit _ _ _ cost hc]
  simpa only [PackageGeometry.total_eq_fin_sum] using
    PackageGeometry.actual_budget package (valid_classical package hv) i j p hij

theorem bundle_disjoint (package : Package (Fin n) RootId) (hd : package.ids.Nodup)
    (G : PackageGeometry.Pieces RootId (Fin n)) (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p) :
    Pairwise (fun i j => Disjoint (bundle package cache i) (bundle package cache j)) := by
  have hroots : (package.allocations.map Allocation.root).Nodup := by
    rw [PackageGeometry.allocation_roots]
    exact hd
  have h := (PackageGeometry.indexedPieces (cachedPieces G cache hsub)
    package.allocations hroots).bundles_disjoint (PackageGeometry.indexedOwner _)
  exact h

theorem bundle_measurable (package : Package (Fin n) RootId)
    (cache : RootId → Fin n → List (Parent n)) (i : Fin n) :
    MeasurableSet (bundle package cache i) :=
  MeasurableSet.iUnion (fun _ => material_measurable _)

theorem bundle_cover (package : Package (Fin n) RootId)
    (cache : RootId → Fin n → List (Parent n)) :
    (⋃ i, bundle package cache i) =
      ⋃ r : Fin package.allocations.length, ⋃ p, material (cache (package.allocations.get r).root p) := by
  simp only [bundle]
  rw [iUnion_comm]
  congr 1
  funext r
  exact (package.allocations.get r).owner.symm.surjective.iUnion_comp
    (fun p => material (cache (package.allocations.get r).root p))

end EnvyFreeResearch.Full.Chores.ComponentPhysical
