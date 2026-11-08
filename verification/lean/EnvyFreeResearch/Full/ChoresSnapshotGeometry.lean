import EnvyFreeResearch.Full.ChoresSnapshotLoop
import Mathlib.Data.List.Pairwise

/-! The generated snapshots are literal disjoint original roots, with
unchanged physical baseline values. These facts follow from the actual
successive Core residues, rather than a disjointness premise on roots. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OrderedUnion InitialPartition PackageGeometry
open scoped Classical BigOperators

variable {n : ℕ}

def Output.piece (out : Output n) (p : Fin n) : Set ℝ := material (out.parents p)
def Output.carrier (out : Output n) : Set ℝ := ⋃ p, out.piece p

variable {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Output n}

theorem Sound.piece_eq (h : Sound cost U c out) (p : Fin n) :
    out.piece p = domainAllocation U c out.outcome p := (h.parent_cache p).2.2

theorem Sound.residue_eq (h : Sound cost U c out) :
    material out.residue = domainResidue U out.outcome := h.residue_cache.2.2

theorem Sound.cover (h : Sound cost U c out) :
    out.carrier ∪ material out.residue = U := by
  simp only [Output.carrier,h.piece_eq,h.residue_eq]
  exact h.core.2.2.1

theorem Sound.pieces_disjoint (h : Sound cost U c out) : Pairwise (fun p q => Disjoint (out.piece p) (out.piece q)) := by
  simpa only [h.piece_eq] using h.core.1

theorem Sound.carrier_residue_disjoint (h : Sound cost U c out) :
    Disjoint out.carrier (material out.residue) := by
  apply disjoint_iUnion_left.mpr
  intro p
  rw [h.piece_eq,h.residue_eq]
  exact h.core.2.1 p

theorem Sound.carrier_subset (h : Sound cost U c out) : out.carrier ⊆ U := by
  rw [← h.cover]
  exact subset_union_left

theorem Sound.residue_subset (h : Sound cost U c out) : material out.residue ⊆ U := by
  rw [← h.cover]
  exact subset_union_right

theorem Sound.envy_free (h : Sound cost U c out) (i j : Fin n) :
    (cost i).real (out.piece i) ≤ (cost i).real (out.piece j) := by
  simpa only [h.piece_eq] using h.core.2.2.2.1 i j

theorem Chain.member_sound {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) (out : Output n) (hm : out ∈ xs) :
    ∃ domain, Sound cost domain c out := by
  induction chain with
  | nil _ _ _ => cases hm
  | @cons U first rest cache hfirst hrest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨U,hfirst⟩
    · exact ih hm

theorem Chain.subsets {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) :
    (∀ out ∈ xs, out.carrier ⊆ U) ∧ material cache ⊆ U := by
  induction chain with
  | nil U cache hc => exact ⟨by simp,hc.2.2 ▸ Subset.rfl⟩
  | @cons U first rest cache hfirst hrest ih =>
    have hr : domainResidue U first.outcome ⊆ U := by
      rw [← hfirst.residue_eq]
      exact hfirst.residue_subset
    refine ⟨?_,ih.2.trans hr⟩
    intro out hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hfirst.carrier_subset
    · exact (ih.1 out hm).trans hr

theorem Chain.roots_disjoint {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) : xs.Pairwise (fun a b => Disjoint a.carrier b.carrier) := by
  induction chain with
  | nil _ _ _ => exact List.Pairwise.nil
  | @cons U first rest cache hfirst hrest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro other hm
    have hsub := (hrest.subsets).1 other hm
    rw [← hfirst.residue_eq] at hsub
    exact hfirst.carrier_residue_disjoint.mono_right hsub

def batchMaterial : List (Output n) → Set ℝ
  | [] => ∅
  | out::rest => out.carrier ∪ batchMaterial rest

theorem batch_material_subset (xs : List (Output n)) (U : Set ℝ)
    (h : ∀ out ∈ xs, out.carrier ⊆ U) : batchMaterial xs ⊆ U := by
  induction xs with
  | nil => exact empty_subset _
  | cons out rest ih =>
    exact union_subset (h out List.mem_cons_self)
      (ih (fun a ha => h a (List.mem_cons_of_mem out ha)))

theorem Chain.cover {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) : batchMaterial xs ∪ material cache = U := by
  induction chain with
  | nil U cache hc => simpa only [batchMaterial,empty_union] using hc.2.2
  | @cons U first rest cache hfirst hrest ih =>
    rw [batchMaterial,union_assoc,ih,← hfirst.residue_eq]
    exact hfirst.cover

theorem Chain.final_residue_disjoint {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) : Disjoint (batchMaterial xs) (material cache) := by
  induction chain with
  | nil _ _ _ => simp [batchMaterial]
  | @cons U first rest cache hfirst hrest ih =>
    apply disjoint_union_left.mpr
    refine ⟨?_,ih⟩
    have hsub := hrest.subsets.2
    rw [← hfirst.residue_eq] at hsub
    exact hfirst.carrier_residue_disjoint.mono_right hsub

/-- Finite occurrence indices are the original root IDs; disjointness is
derived from generation, including coincident empty snapshot records. -/
def Chain.pieces {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) : Pieces (Fin xs.length) (Fin n) where
  piece := fun r p => (xs.get r).piece p
  measurable := fun r p => material_measurable _
  disjoint := by
    intro a b hab
    by_cases hr : a.1 = b.1
    · have hp : a.2 ≠ b.2 := fun hp => hab (Prod.ext hr hp)
      obtain ⟨domain,hsound⟩ := chain.member_sound (xs.get a.1) (List.get_mem _ _)
      rw [← hr]
      exact hsound.pieces_disjoint hp
    · have hd : Disjoint (xs.get a.1).carrier (xs.get b.1).carrier := by
        rcases lt_or_gt_of_ne hr with hlt | hgt
        · exact List.pairwise_iff_get.mp chain.roots_disjoint a.1 b.1 hlt
        · exact (List.pairwise_iff_get.mp chain.roots_disjoint b.1 a.1 hgt).symm
      exact hd.mono (subset_iUnion (fun p => (xs.get a.1).piece p) a.2)
        (subset_iUnion (fun p => (xs.get b.1).piece p) b.2)

theorem Chain.aggregate_envy_free {xs : List (Output n)} {cache : List (Parent n)}
    (chain : Chain cost c U xs cache) :
    ∀ i j, (cost i).real (chain.pieces.bundle (fun _ => Equiv.refl _) i) ≤
      (cost i).real (chain.pieces.bundle (fun _ => Equiv.refl _) j) := by
  intro i j
  rw [Pieces.bundle_value, Pieces.bundle_value]
  apply Finset.sum_le_sum
  intro r _
  obtain ⟨domain,hsound⟩ := chain.member_sound (xs.get r) (List.get_mem _ _)
  exact hsound.envy_free i j

end EnvyFreeResearch.Full.Chores.Snapshot
