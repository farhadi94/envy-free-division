import EnvyFreeResearch.Full.ChoresPackageProposal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Nodup

/-! The finite package ledger controls the costs of literal disjoint
allocations. In particular, the live frame is included in every physical
bundle even though the package credit table stores frozen roots only. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PackageGeometry
open Set MeasureTheory ChoreComposition
open scoped Classical BigOperators

variable {Agent Root : Type*}

theorem allocation_roots (s : Package Agent Root) :
    s.allocations.map Allocation.root = s.ids := by
  simp [Package.allocations, Package.ids, List.map_map, Frame.allocation,
    Function.comp_def]

theorem actual_credit_total (s : Package Agent Root) (hs : s.Valid) (i p : Agent) :
    total s.allocations (fun a => a.credit i p) = s.credit i p := by
  cases he : s.live with
  | none => simp [Package.allocations, Package.credit, he]
  | some f =>
    simp [Package.allocations, Package.credit, he, total_append,
      frame_credit_zero f (hs.live_good f he)]

theorem actual_debit_total_le (s : Package Agent Root) (hs : s.Valid) (i j p : Agent) :
    total s.allocations (fun a => a.debit i j p) ≤ s.debit i j p+s.reserve i j p := by
  cases he : s.live with
  | none => simp [Package.allocations, Package.debit, Package.reserve, he]
  | some f =>
    simpa [Package.allocations, Package.debit, Package.reserve, he, total_append] using
      add_le_add_left (frame_debit_le_reserve f (hs.live_good f he) i j p) (s.debit i j p)

theorem actual_budget (s : Package Agent Root) (hs : s.Valid) (i j p : Agent) (hij : i ≠ j) :
    total s.allocations (fun a => a.debit i j p) ≤ total s.allocations (fun a => a.credit i p) := by
  rw [actual_credit_total s hs]
  exact (actual_debit_total_le s hs i j p).trans (hs.budget i j p hij)

theorem pool_actual_budget (pool : List (Package Agent Root)) (hp : PoolValid pool)
    (i j p : Agent) (hij : i ≠ j) :
    total (pool.flatMap Package.allocations) (fun a => a.debit i j p) ≤
      total (pool.flatMap Package.allocations) (fun a => a.credit i p) := by
  simp only [total_flatMap]
  exact total_mono pool _ _ (fun s hs => actual_budget s (hp s hs) i j p hij)

theorem pool_allocation_roots (pool : List (Package Agent Root)) :
    (pool.flatMap Package.allocations).map Allocation.root = pool.flatMap Package.ids := by
  induction pool with
  | nil => rfl
  | cons s rest ih => simp only [List.flatMap_cons, List.map_append, allocation_roots, ih]

theorem total_eq_fin_sum {α : Type*} (xs : List α) (f : α → ℝ) :
    total xs f = ∑ r : Fin xs.length, f (xs.get r) := by
  calc
    total xs f = (List.ofFn (fun r : Fin xs.length => f (xs.get r))).sum := by
      exact (congrArg List.sum (List.ofFn_getElem_eq_map xs f)).symm
    _ = _ := List.sum_ofFn

def Pieces.reindex {Index : Type*} (G : Pieces Root Agent) (f : Index → Root)
    (hf : Function.Injective f) : Pieces Index Agent where
  piece := fun r p => G.piece (f r) p
  measurable := fun r p => G.measurable (f r) p
  disjoint := by
    intro a b hab
    apply @G.disjoint (f a.1,a.2) (f b.1,b.2)
    intro h
    apply hab
    exact Prod.ext (hf (congrArg (fun z : Root × Agent => z.1) h))
      (congrArg (fun z : Root × Agent => z.2) h)

theorem list_roots_injective (as : List (Allocation Agent Root))
    (h : (as.map Allocation.root).Nodup) :
    Function.Injective (fun r : Fin as.length => (as.get r).root) := by
  intro i j heq
  have hh := List.nodup_iff_injective_get.mp h
  have hget : (as.map Allocation.root).get ⟨i.val, by simp⟩ =
      (as.map Allocation.root).get ⟨j.val, by simp⟩ := by
    simpa using heq
  exact Fin.ext (congrArg (fun r : Fin (as.map Allocation.root).length => r.val) (hh hget))

def indexedPieces (G : Pieces Root Agent) (as : List (Allocation Agent Root))
    (h : (as.map Allocation.root).Nodup) : Pieces (Fin as.length) Agent :=
  G.reindex (fun r => (as.get r).root) (list_roots_injective as h)

def indexedOwner (as : List (Allocation Agent Root)) : Fin as.length → Equiv.Perm Agent :=
  fun r => (as.get r).owner

def indexedBaseline (as : List (Allocation Agent Root)) : Fin as.length → Agent → ℝ :=
  fun r => (as.get r).baseline

theorem indexed_credit (G : Pieces Root Agent) (as : List (Allocation Agent Root))
    (h : (as.map Allocation.root).Nodup) (cost : Agent → Measure ℝ)
    (hv : ∀ a ∈ as, ∀ i p, a.cost i p = (cost i).real (G.piece a.root p))
    (r : Fin as.length) (i p : Agent) :
    (indexedPieces G as h).credit (indexedOwner as) cost (indexedBaseline as) r i p =
      (as.get r).credit i p := by
  simp only [Pieces.credit, indexedPieces, Pieces.reindex, indexedOwner, indexedBaseline,
    Allocation.credit, hv (as.get r) (List.get_mem as r) i p]
  rfl

theorem indexed_debit (G : Pieces Root Agent) (as : List (Allocation Agent Root))
    (h : (as.map Allocation.root).Nodup) (cost : Agent → Measure ℝ)
    (hv : ∀ a ∈ as, ∀ i p, a.cost i p = (cost i).real (G.piece a.root p))
    (r : Fin as.length) (i j p : Agent) :
    (indexedPieces G as h).debit (indexedOwner as) cost (indexedBaseline as) r i j p =
      (as.get r).debit i j p := by
  simp only [Pieces.debit, indexedPieces, Pieces.reindex, indexedOwner, indexedBaseline,
    Allocation.debit, R7Chores.clipped, hv (as.get r) (List.get_mem as r) i p]
  rfl

/-- Ledger validity implies envy-freeness for the actual measurable pieces,
once the stored root cost tables have been realized by those pieces. -/
theorem physical_pool_envy_free [Fintype Agent]
    (pool : List (Package Agent Root)) (hp : PoolValid pool) (hd : PoolDistinct pool)
    (G : Pieces Root Agent) (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (hv : ∀ a ∈ pool.flatMap Package.allocations, ∀ i p,
      a.cost i p = (cost i).real (G.piece a.root p)) :
    let as := pool.flatMap Package.allocations
    let hs : (as.map Allocation.root).Nodup := by rw [pool_allocation_roots]; exact hd
    let X := (indexedPieces G as hs).bundle (indexedOwner as)
    ∀ i j, (cost i).real (X i) ≤ (cost i).real (X j) := by
  dsimp only
  apply Pieces.envy_free _ _ _ (indexedBaseline (pool.flatMap Package.allocations))
  intro i j hij p
  simp only [indexed_debit G _ _ cost hv, indexed_credit G _ _ cost hv]
  simpa only [total_eq_fin_sum] using pool_actual_budget pool hp i j p hij

/-- The physical margin retains the sum of every ancestor's positive
deviation, including ancestors with different eligible sets. -/
theorem physical_pool_surplus [Fintype Agent]
    (pool : List (Package Agent Root)) (hp : PoolValid pool) (hd : PoolDistinct pool)
    (G : Pieces Root Agent) (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (hv : ∀ a ∈ pool.flatMap Package.allocations, ∀ i p,
      a.cost i p = (cost i).real (G.piece a.root p)) (i j : Agent) (hij : i ≠ j) :
    let as := pool.flatMap Package.allocations
    let hs : (as.map Allocation.root).Nodup := by rw [pool_allocation_roots]; exact hd
    let X := (indexedPieces G as hs).bundle (indexedOwner as)
    total as (fun a => max 0 ((cost i).real (G.piece a.root (a.owner.symm j))-a.baseline i)) ≤
      (cost i).real (X j)-(cost i).real (X i) := by
  dsimp only
  have h := (indexedPieces G (pool.flatMap Package.allocations)
    (by rw [pool_allocation_roots]; exact hd)).surplus
      (indexedOwner _) cost (indexedBaseline _) i j (fun p => by
        simp only [indexed_debit G _ _ cost hv, indexed_credit G _ _ cost hv]
        simpa only [total_eq_fin_sum] using pool_actual_budget pool hp i j p hij)
  simpa only [total_eq_fin_sum,indexedPieces,Pieces.reindex,Pieces.assigned,
    indexedOwner,indexedBaseline] using h

theorem actual_pool_credit (pool : List (Package Agent Root)) (hp : PoolValid pool) (i p : Agent) :
    total (pool.flatMap Package.allocations) (fun a => a.credit i p) =
      total pool (fun s => s.credit i p) := by
  rw [total_flatMap]
  unfold total
  congr 1
  apply List.map_congr_left
  intro s hs
  exact actual_credit_total s (hp s hs) i p

/-- Only frozen credits appear on the right; all live and frozen physical
pieces appear in the bundle on the left. This identity is derived rather
than imposed as part of a package invariant. -/
theorem physical_pool_own_identity [Fintype Agent]
    (pool : List (Package Agent Root)) (hp : PoolValid pool) (hd : PoolDistinct pool)
    (G : Pieces Root Agent) (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (hv : ∀ a ∈ pool.flatMap Package.allocations, ∀ i p,
      a.cost i p = (cost i).real (G.piece a.root p)) (i : Agent) :
    let as := pool.flatMap Package.allocations
    let hs : (as.map Allocation.root).Nodup := by rw [pool_allocation_roots]; exact hd
    let X := (indexedPieces G as hs).bundle (indexedOwner as)
    (cost i).real (X i) = total as (fun a => a.baseline i)-∑ p, total pool (fun s => s.credit i p) := by
  dsimp only
  rw [Pieces.own_identity _ _ _ (indexedBaseline _)]
  simp only [indexed_credit G _ _ cost hv,indexedBaseline]
  congr 1
  · exact (total_eq_fin_sum (pool.flatMap Package.allocations) (fun a => a.baseline i)).symm
  · apply Finset.sum_congr rfl
    intro p _
    rw [← actual_pool_credit pool hp]
    exact (total_eq_fin_sum (pool.flatMap Package.allocations) (fun a => a.credit i p)).symm

end EnvyFreeResearch.Full.Chores.PackageGeometry
