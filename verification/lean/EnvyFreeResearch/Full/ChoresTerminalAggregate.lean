import EnvyFreeResearch.Full.ChoresOuterPool
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! Physical positive-surplus witnesses survive aggregation of the entire
package pool, including frozen ancestors and rejected packages. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

private theorem term_le_total {α : Type*} (xs : List α) (f : α → ℝ)
    (hn : ∀ x ∈ xs, 0 ≤ f x) (a : α) (ha : a ∈ xs) : f a ≤ total xs f := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [total_cons]
      exact le_add_of_nonneg_right (total_nonnegative bs f (fun x hx => hn x (by simp [hx])))
    · rw [total_cons]
      exact (ih (fun x hx => hn x (by simp [hx])) ha).trans
        (le_add_of_nonneg_left (hn b (by simp)))

variable {n : ℕ} {RootId : Type*}
  (pool : List (Package (Fin n) RootId)) (hp : PoolValid pool) (hd : PoolDistinct pool)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (cache : RootId → Fin n → List (Parent n))
  (hsub : ∀ root p, material (cache root p) ⊆ G.piece root p)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
  (hcost : ∀ a ∈ pool.flatMap Package.allocations, ∀ i p,
    a.cost i p=(cost i).real (material (cache a.root p)))

include hp hd hcost hsub

theorem pool_physical_surplus (i j : Fin n) (hij : i ≠ j) :
    total (pool.flatMap Package.allocations)
      (fun a => max 0 ((cost i).real (material (cache a.root (a.owner.symm j)))-a.baseline i)) ≤
    (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache j)-
      (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache i) := by
  have hp' : @PoolValid (Fin n) RootId (fun a b => Classical.propDecidable (a=b)) pool := by
    have heq : instDecidableEqFin n = (fun a b : Fin n => Classical.propDecidable (a=b)) :=
      Subsingleton.elim _ _
    rw [← heq]
    exact hp
  have h := PackageGeometry.physical_pool_surplus pool hp' hd
    (ComponentPhysical.cachedPieces G cache hsub) cost hcost i j hij
  have hb (k : Fin n) : ComponentPhysical.bundle (Outer.closePool pool) cache k =
      ⋃ s : Fin (pool.flatMap Package.allocations).length,
        material (cache ((pool.flatMap Package.allocations).get s).root
          (((pool.flatMap Package.allocations).get s).owner.symm k)) := by
    unfold ComponentPhysical.bundle
    rw [Outer.close_pool_allocations]
  rw [hb j,hb i]
  exact h

theorem pool_witness_margin (i j : Fin n) (hij : i ≠ j)
    (a : ChoreComposition.Allocation (Fin n) RootId)
    (ha : a ∈ pool.flatMap Package.allocations) (D : ℝ)
    (hwitness : D ≤ (cost i).real (material (cache a.root (a.owner.symm j)))-a.baseline i) :
    D ≤ (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache j)-
      (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache i) := by
  exact (hwitness.trans (le_max_right _ _)).trans
    ((term_le_total _ (fun b => max 0
      ((cost i).real (material (cache b.root (b.owner.symm j)))-b.baseline i))
      (fun _ _ => le_max_left _ _) a ha).trans
      (pool_physical_surplus pool hp hd G cache hsub cost hcost i j hij))

theorem pool_recipient_witness_margin (i j p : Fin n) (hij : i ≠ j)
    (a : ChoreComposition.Allocation (Fin n) RootId)
    (ha : a ∈ pool.flatMap Package.allocations) (howner : a.owner p=j) (D : ℝ)
    (hwitness : D ≤ (cost i).real (material (cache a.root p))-a.baseline i) :
    D ≤ (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache j)-
      (cost i).real (ComponentPhysical.bundle (Outer.closePool pool) cache i) := by
  apply pool_witness_margin pool hp hd G cache hsub cost hcost i j hij a ha D
  simpa only [← howner, Equiv.symm_apply_apply] using hwitness

end EnvyFreeResearch.Full.Chores.Terminal
