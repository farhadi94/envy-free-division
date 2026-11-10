import EnvyFreeResearch.Full.RefinedChoresTerminalScans
import EnvyFreeResearch.Full.RefinedChoresTerminalAggregatePhysical
import EnvyFreeResearch.Full.ChoresTerminalResidue

/-! Physical exhaustion margins for independently scanned source components. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
open Set MeasureTheory IntervalOracle
open Chores Chores.InitialPartition Chores.OrderedUnion Chores.Snapshot Chores.Frontier
open Chores.ComponentRecording Chores.ComponentPayments Chores.ComponentExtraction
open RefinedChoresTerminalScans
open scoped Classical
variable {n : ℕ} {Root : Type*} [Fintype Root] [Nonempty Root]
    (original : Root → Snapshot.Output n) (p : Fin n)
    (components : Root → Finset (Fin n))
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ s, ∃ U, Snapshot.Sound cost U c (original s))
    (xs : List (Snapshot.Output n)) (index : Root → Fin xs.length)
    (horiginal : ∀ s, original s = xs.get (index s)) (R : Set ℝ) (H : ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (A B : Finset (Fin n)) (representatives : Root → Fin n → Fin n)
    (hclass : ∀ s, Reveal.classify (original s).equalizers p (fun i => (cost i).real R) H
      (components s) (representatives s) = .inl (.inl (A,B)))
    (out : RefinedChoresClosed.Result (Root := Root) A)
    (hparts : PartsCorrect cost (domains
      (blocks original p (fun i => (cost i).real R) H components) (fun _ => p)) Subtype.val out)

    (hwhole : ∃ j : A, material (out.parts j).suffixParts =
      blocks original p (fun i => (cost i).real R) H components (out.allocation.assigned j) p)
include hsound horiginal hsep hr hH hscale hclass hparts hwhole

theorem atomic_extracted_bounds :
    B.Nonempty ∧ B ≠ Finset.univ ∧
    (∀ i ∈ B, H*(cost i).real R ≤ (cost i).real (extracted out)) ∧
    (∀ i, i ∉ B → (cost i).real (extracted out) ≤ (n : ℝ)^2*(cost i).real R/H) := by
  have hb (s : Root) : B.Nonempty ∧ B ≠ Finset.univ ∧
      Terminal.atom (xs.get (index s)) p (fun i => (cost i).real R) H (components s) ⊆
        material (Terminal.offer (xs.get (index s)) p (fun i => (cost i).real R) H (components s)) ∧
      (∀ i ∈ B, H*(cost i).real R ≤ (cost i).real
        (Terminal.atom (xs.get (index s)) p (fun i => (cost i).real R) H (components s))) ∧
      (∀ i, i ∉ B → (cost i).real
        (material (Terminal.offer (xs.get (index s)) p (fun i => (cost i).real R) H (components s))) ≤
        (n : ℝ)*(cost i).real R/H) := by
    obtain ⟨U,hs⟩ := hsound s
    rw [horiginal s] at hs
    exact Terminal.scan_atomic_bounds hsep (index s) hs p hr hH hscale
      (components s) (representatives s) A B (by simpa only [horiginal s] using hclass s)
  let s : Root := Classical.choice inferInstance
  refine ⟨(hb s).1,(hb s).2.1,?_,?_⟩
  · intro i hi
    apply extracted_large (Subtype.val : A → Fin n) (fun _ => p) out cost
      (blocks original p (fun i => (cost i).real R) H components) i H ((cost i).real R)
      (fun s => Terminal.atom (original s) p (fun i => (cost i).real R) H (components s))
    · intro s
      simpa only [horiginal s] using (hb s).2.2.2.1 i hi
    · intro j
      simpa only [blocks,offer,horiginal] using (hb (out.allocation.assigned j)).2.2.1
    · exact hwhole
  · intro i hi
    apply extracted_small (Subtype.val : A → Fin n) (fun _ => p) out cost
      (blocks original p (fun i => (cost i).real R) H components) hparts i H
      ((cost i).real R) (by linarith) (hr i).le
    · simpa only [Fintype.card_coe, Fintype.card_fin] using (Finset.card_le_univ A)
    · intro j
      simpa only [blocks,offer,horiginal] using (hb (out.allocation.assigned j)).2.2.2.2 i hi

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
