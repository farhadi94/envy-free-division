import EnvyFreeResearch.Full.ChoresComponentPhysicalEF
import EnvyFreeResearch.Full.ChoresCompletionAllocation

/-! Closing an entire pool and assembling its literal physical allocation.
All live roots and frozen ancestors appear exactly once. No oracle call
is needed for closure, cache assembly, or the resulting EF proof. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*}

def closePool (pool : List (Package (Fin n) RootId)) : Package (Fin n) RootId :=
  ⟨pool.flatMap Package.allocations,none⟩

theorem actual_credit_nonnegative (package : Package (Fin n) RootId) (hp : package.Valid)
    (a : ChoreComposition.Allocation (Fin n) RootId) (ha : a ∈ package.allocations) (i p : Fin n) :
    0 ≤ a.credit i p := by
  obtain ha | ha := List.mem_append.mp ha
  · exact hp.frozen_nonnegative a ha i p
  · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ha
    have hf' : package.live=some f := Option.mem_toList.mp hf
    rw [frame_credit_zero f (hp.live_good f hf')]

theorem close_pool_valid (pool : List (Package (Fin n) RootId)) (hp : PoolValid pool) :
    (closePool pool).Valid := by
  constructor
  · intro f hf
    cases hf
  · intro a ha i p
    obtain ⟨package,hpackage,ha⟩ := List.mem_flatMap.mp ha
    exact actual_credit_nonnegative package (hp package hpackage) a ha i p
  · intro i j p hij
    change total (pool.flatMap Package.allocations) (fun a => a.debit i j p)+0 ≤
      total (pool.flatMap Package.allocations) (fun a => a.credit i p)
    rw [add_zero]
    have hp' : @PoolValid (Fin n) RootId (fun a b => Classical.propDecidable (a=b)) pool := by
      have heq : (instDecidableEqFin n)=(fun a b : Fin n => Classical.propDecidable (a=b)) := Subsingleton.elim _ _
      rw [← heq]
      exact hp
    have h := PackageGeometry.pool_actual_budget pool hp' i j p hij
    have heq : (instDecidableEqFin n)=(fun a b : Fin n => Classical.propDecidable (a=b)) := Subsingleton.elim _ _
    rw [← heq] at h
    exact h

theorem close_pool_allocations (pool : List (Package (Fin n) RootId)) :
    (closePool pool).allocations=pool.flatMap Package.allocations := by
  simp only [closePool,Package.allocations,Option.toList_none,List.map_nil,List.append_nil]

theorem close_pool_ids (pool : List (Package (Fin n) RootId)) :
    (closePool pool).ids=pool.flatMap Package.ids := by
  rw [← PackageGeometry.allocation_roots,close_pool_allocations,PackageGeometry.pool_allocation_roots]

def poolAllocation (pool : List (Package (Fin n) RootId))
    (cache : RootId → Fin n → List (Parent n)) : Completion.Allocation n (Fin n) :=
  ⟨ComponentPhysical.bundleCache (closePool pool) cache⟩

def poolDomain (pool : List (Package (Fin n) RootId))
    (cache : RootId → Fin n → List (Parent n)) : Set ℝ :=
  ⋃ i, ComponentPhysical.bundle (closePool pool) cache i

theorem pool_allocation_sound (pool : List (Package (Fin n) RootId)) (hp : PoolValid pool)
    (hd : PoolDistinct pool) (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (hv : ∀ r p, Valid (measureProfile cost) (cache r p) ∧ Ordered (cache r p))
    (hcost : ∀ a ∈ pool.flatMap Package.allocations, ∀ i p,
      a.cost i p=(cost i).real (material (cache a.root p))) :
    (poolAllocation pool cache).Sound cost id (poolDomain pool cache) := by
  have hids : (closePool pool).ids.Nodup := by rw [close_pool_ids]; exact hd
  have hc : ∀ i, CacheValid (measureProfile cost) (ComponentPhysical.bundle (closePool pool) cache i)
      ((poolAllocation pool cache).pieces i) :=
    fun i => ComponentPhysical.bundle_cache_correct _ hids G cache hsub _ hv i
  have hvalues : ∀ a ∈ (closePool pool).allocations, ∀ i p,
      a.cost i p=(cost i).real (material (cache a.root p)) := by
    simpa only [close_pool_allocations] using hcost
  constructor
  · intro i
    exact ⟨(hc i).1,(hc i).2.1,rfl⟩
  · intro i j hij
    rw [(hc i).2.2,(hc j).2.2]
    exact ComponentPhysical.bundle_disjoint _ hids G cache hsub hij
  · simp only [(hc _).2.2,poolDomain]
  · intro i j
    rw [(hc i).2.2,(hc j).2.2]
    exact ComponentPhysical.bundle_envy_free _ (close_pool_valid pool hp) hids G cache hsub cost hvalues i j

theorem pool_domain_all_roots [Fintype RootId] [DecidableEq RootId]
    (pool : List (Package (Fin n) RootId)) (cache : RootId → Fin n → List (Parent n))
    (hids : (pool.flatMap Package.ids).Perm Finset.univ.toList) :
    poolDomain pool cache=⋃ r, ⋃ p, material (cache r p) := by
  have hall : ∀ r : RootId, ∃ a ∈ (closePool pool).allocations, a.root=r := by
    intro r
    have hr : r ∈ (closePool pool).ids := by
      rw [close_pool_ids]
      exact hids.mem_iff.mpr (by simp)
    rw [← PackageGeometry.allocation_roots] at hr
    exact List.mem_map.mp hr
  rw [poolDomain,ComponentPhysical.bundle_cover]
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    obtain ⟨p,hx⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨((closePool pool).allocations.get a).root,mem_iUnion.mpr ⟨p,hx⟩⟩
  · intro hx
    obtain ⟨r,hr⟩ := mem_iUnion.mp hx
    obtain ⟨p,hp⟩ := mem_iUnion.mp hr
    obtain ⟨a,ha,har⟩ := hall r
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp ha
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨p,by simpa only [hj,har] using hp⟩⟩

end EnvyFreeResearch.Full.Chores.Outer
