import EnvyFreeResearch.Full.ChoresPreprocessing
import EnvyFreeResearch.Full.ChoresProtectedPivot
import EnvyFreeResearch.Full.ChoresClearanceLength

/-! All clearance allocations remain literal disjoint, envy-free bundles.
These lemmas expose the physical output of preprocessing together with its
separated original table and protected label. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OrderedUnion InitialPartition PackageGeometry
open scoped Classical BigOperators

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

def AnyChain.pieces {U : Set ℝ} {xs : List (Output n)} {cache : List (Parent n)}
    (chain : AnyChain cost U xs cache) : Pieces (Fin xs.length) (Fin n) where
  piece := fun r p => (xs.get r).piece p
  measurable := fun r p => material_measurable _
  disjoint := by
    intro a b hab
    by_cases hr : a.1 = b.1
    · have hp : a.2 ≠ b.2 := fun hp => hab (Prod.ext hr hp)
      obtain ⟨c,domain,hsound⟩ := chain.member_sound (xs.get a.1) (List.get_mem _ _)
      rw [← hr]
      exact hsound.pieces_disjoint hp
    · have hd : Disjoint (xs.get a.1).carrier (xs.get b.1).carrier := by
        rcases lt_or_gt_of_ne hr with hlt | hgt
        · exact List.pairwise_iff_get.mp chain.roots_disjoint a.1 b.1 hlt
        · exact (List.pairwise_iff_get.mp chain.roots_disjoint b.1 a.1 hgt).symm
      exact hd.mono (subset_iUnion (fun p => (xs.get a.1).piece p) a.2)
        (subset_iUnion (fun p => (xs.get b.1).piece p) b.2)

theorem AnyChain.aggregate_envy_free {U : Set ℝ} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : AnyChain cost U xs cache) :
    ∀ i j, (cost i).real (chain.pieces.bundle (fun _ => Equiv.refl _) i) ≤
      (cost i).real (chain.pieces.bundle (fun _ => Equiv.refl _) j) := by
  intro i j
  rw [Pieces.bundle_value,Pieces.bundle_value]
  apply Finset.sum_le_sum
  intro r _
  obtain ⟨c,domain,hsound⟩ := chain.member_sound (xs.get r) (List.get_mem _ _)
  exact hsound.envy_free i j

end EnvyFreeResearch.Full.Chores.Snapshot

namespace EnvyFreeResearch.Full.Chores.Preprocessing
open Set MeasureTheory OrderedUnion InitialPartition Snapshot ProtectedPivot
open scoped Classical

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem output_accounting {U : Set ℝ} {c : Fin n} (out : Output n)
    (horiginal : Chain cost c U out.originals out.middle)
    (hclear : AnyChain cost (material out.middle) out.clearance out.residue) :
    AnyChain cost U (out.originals++out.clearance) out.residue ∧
      batchMaterial (out.originals++out.clearance) ∪ material out.residue = U ∧
      Disjoint (batchMaterial (out.originals++out.clearance)) (material out.residue) := by
  have hchain := horiginal.any.append hclear
  exact ⟨hchain,hchain.cover,hchain.final_residue_disjoint⟩

theorem protected_label {U : Set ℝ} {c : Fin n} (hn : 2 ≤ n) (out : Output n)
    (horiginal : Chain cost c U out.originals out.middle)
    (hclear : AnyChain cost (material out.middle) out.clearance out.residue)
    (hr : 0 < (cost c).real (material out.residue))
    (H : ℝ) (hH : (n-1 : ℕ) < H) (S : ℕ)
    (hcount : (S-1)*(n-1) < out.originals.length) :
    ∃ p : Fin n, p ≠ c ∧ ∃ selected : Finset (Fin out.originals.length), selected.card = S ∧
      ∀ s ∈ selected, c ∉ eligible (out.originals.get s) H
        (fun i => (cost i).real (material out.residue)) p :=
  common_omitted_exact hn cost c out.originals out.middle horiginal hclear.subsets.2 hr H hH S hcount

end EnvyFreeResearch.Full.Chores.Preprocessing
