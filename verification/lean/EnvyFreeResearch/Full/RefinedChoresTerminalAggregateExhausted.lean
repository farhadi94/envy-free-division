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
    (A : Finset (Fin n)) (representatives : Root → Fin n → Fin n)
    (hclass : ∀ s, Reveal.classify (original s).equalizers p (fun i => (cost i).real R) H
      (components s) (representatives s) = .inl (.inr A))
    (out : RefinedChoresClosed.Result (Root := Root) A)
    (hparts : PartsCorrect cost (domains
      (blocks original p (fun i => (cost i).real R) H components) (fun _ => p)) Subtype.val out)
include hsound horiginal hsep hr hH hscale hclass hparts

theorem exhausted_scan_bounds (s : Root) :
    (∀ i, (cost i).real (blocks original p (fun i => (cost i).real R) H components s p) ≤
      (n : ℝ)*(cost i).real R/H) ∧
    (∀ i, i ∉ A → H*(cost i).real R ≤ gaps original s p i) := by
  obtain ⟨U,hs⟩ := hsound s
  rw [horiginal s] at hs
  have hb := Terminal.scan_exhausted_bounds hsep (index s) hs p hr hH hscale
    (components s) (representatives s) A (by simpa only [horiginal s] using hclass s)
  simpa only [blocks,offer,gaps,horiginal s] using And.intro hb.1 hb.2.1

theorem exhausted_donor_deviation (i : Fin n) (hi : i ∉ A) (j : A) :
    (H-(n : ℝ)/H)*(cost i).real R ≤
      (cost i).real ((original (out.allocation.assigned j)).piece p \
        material (out.parts j).suffixParts)-
      Equalizers.baselines (original (out.allocation.assigned j)).parents i := by
  let s := out.allocation.assigned j
  have hs := (hsound s).choose_spec
  have hb := exhausted_scan_bounds original p components cost c hsound xs index horiginal R H
    hsep hr hH hscale A representatives hclass out hparts s
  have hblock : blocks original p (fun i => (cost i).real R) H components s p ⊆
      (original s).piece p := by
    change material (Terminal.offer _ _ _ _ _) ⊆ _
    have hc : material (Terminal.offer (original s) p (fun i => (cost i).real R) H (components s)) =
        (original s).piece p \ material (Terminal.front (original s) p (fun i => (cost i).real R) H (components s)) :=
      Frontier.offer_complement cost _ _ (snapshot_parent_cache hs p) _ p _
        (snapshot_equalizers hs p) (hs.own_equalizers p).1 _
    rw [hc]
    exact sdiff_subset
  have hsub := (suffix_subset cost _ (Subtype.val : A → Fin n) (fun _ => p) out hparts j).trans hblock
  rw [measureReal_sdiff hsub (material_measurable _)]
  have hrem := (measureReal_mono (μ := cost i)
    (suffix_subset cost _ (Subtype.val : A → Fin n) (fun _ => p) out hparts j)).trans (hb.1 i)
  have hlarge := hb.2 i hi
  change H*(cost i).real R ≤ Clearance.gap (original s) i p at hlarge
  rw [Terminal.gap_eq hs] at hlarge
  change (H-(n : ℝ)/H)*(cost i).real R ≤
    (cost i).real ((original s).piece p) - (cost i).real (material (out.parts j).suffixParts) - _
  have heq : (H-(n : ℝ)/H)*(cost i).real R = H*(cost i).real R - (n : ℝ)*(cost i).real R/H := by ring
  rw [heq]
  linarith

theorem exhausted_extracted_small (i : Fin n) :
    (cost i).real (extracted out) ≤ (n : ℝ)^2*(cost i).real R/H := by
  apply extracted_small (Subtype.val : A → Fin n) (fun _ => p) out cost _ hparts i H
    ((cost i).real R) (by linarith) (hr i).le
    (by simpa using A.card_le_univ)
  intro j
  exact (exhausted_scan_bounds original p components cost c hsound xs index horiginal R H
    hsep hr hH hscale A representatives hclass out hparts _).1 i

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
