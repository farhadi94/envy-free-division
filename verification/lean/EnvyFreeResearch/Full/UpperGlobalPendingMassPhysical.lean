import EnvyFreeResearch.Full.UpperGlobalPendingMassBounds
import EnvyFreeResearch.Full.UpperGlobalPhysicalPending

/-! The physical pending-state invariant supplies the separation and cache
identities used in the final Repair input bounds. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
include hp

theorem pending_shrunk_subset (j : Fin n) :
    domain (p.shrunk j).cells ⊆ domain p.anchor.residue.cells := by
  rw [← hp.cover]
  intro x hx
  exact Or.inl (Or.inl (mem_iUnion.mpr ⟨j,hx⟩))

theorem pending_snapshot_subset (j : Fin n) :
    domain (p.snapshot j).cells ⊆ domain p.anchor.residue.cells := by
  rw [← hp.cover]
  intro x hx
  exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j,hx⟩))

theorem pending_saved_shrunk_disjoint (j : Fin n) :
    Disjoint (domain (p.anchor.bundles j).cells) (domain (p.shrunk j).cells) :=
  (hp.anchor.separate j).mono_right (pending_shrunk_subset μ whole p hp j)

theorem pending_saved_snapshot_disjoint (j : Fin n) :
    Disjoint (domain (p.anchor.bundles j).cells) (domain (p.snapshot (p.permutation j)).cells) :=
  (hp.anchor.separate j).mono_right (pending_snapshot_subset μ whole p hp _)

theorem pending_permutation_active (j : Fin n) (hj : j ∈ p.anchor.active) :
    p.permutation j ∈ p.anchor.active := by
  by_contra hn
  have he : p.permutation j = j := p.permutation.injective (hp.permutation_frozen _ hn)
  exact hn (he.symm ▸ hj)

theorem pending_physical_margin (direction : Direction) (i j : Fin n) :
    margin direction (value μ p.endowments) i j =
      margin direction (value μ p.anchor.bundles) i j +
      margin direction (value μ p.shrunk) i j +
      margin direction (value μ p.snapshot) i (p.permutation j) -
      margin direction (value μ p.snapshot) i (p.permutation i) :=
  pending_margin_identity μ p (pending_saved_shrunk_disjoint μ whole p hp)
    (pending_saved_snapshot_disjoint μ whole p hp) (fun j => hp.cross j _) direction i j

theorem pending_snapshot_cache (i j : Fin n) :
    total (p.snapshot j) i = value μ p.snapshot i j :=
  total_correct μ (p.snapshot j) (hp.snapshot_wf j) i

theorem pending_snapshot_margin_cache (direction : Direction) (i j : Fin n) :
    margin direction (fun a b => total (p.snapshot b) a) i j =
      margin direction (value μ p.snapshot) i j := by
  cases direction <;> simp only [margin,pending_snapshot_cache μ whole p hp]

theorem pending_buffer_cache (i : Fin n) :
    total p.buffer i = (μ i).real (domain p.buffer.cells) :=
  total_correct μ p.buffer hp.buffer_wf i

theorem pending_endowment_cache (i j : Fin n) :
    total (p.endowments j) i = value μ p.endowments i j := by
  exact total_correct μ (p.endowments j)
    ((pending_provisional_physical μ whole p hp).bundles_wellFormed j) i

end EnvyFreeResearch.Full.UpperGlobalPhysical
