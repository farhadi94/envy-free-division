import EnvyFreeResearch.Full.ChoresFrontierPhysical
import EnvyFreeResearch.Full.ChoresTrackedTable

/-! Clearance supplies the physical scan's hypotheses from the literal
immutable table of generated snapshots. No classification or successful
compensation certificate is assumed at this interface. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers Snapshot
open scoped Classical

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Output n}

theorem snapshot_parent_cache (hs : Sound cost U c out) (p : Fin n) :
    CacheValid (measureProfile cost) (out.piece p) (out.parents p) :=
  ⟨(hs.parent_cache p).1,(hs.parent_cache p).2.1,rfl⟩

theorem snapshot_equalizers (hs : Sound cost U c out) (p i : Fin n) :
    Equalizers.Correct cost (out.piece p) (baselines out.parents) i (out.equalizers (p,i)) := by
  rw [hs.piece_eq]
  exact hs.equalizers p i

theorem snapshot_tail_gap (hs : Sound cost U c out) (p i : Fin n) :
    tailCost (weight out.equalizers p) i (rankOf out.equalizers p i)=Clearance.gap out i p := by
  rw [gap_is_tail cost (out.piece p) (out.parents p) (snapshot_parent_cache hs p)
    out.equalizers p (baselines out.parents) (snapshot_equalizers hs p) (hs.own_equalizers p).1]
  rw [Clearance.gap,baselines,Output.piece,
    material_value cost _ (hs.parent_cache p).1 (hs.parent_cache p).2.1]

theorem tracked_gaps {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (s : Fin xs.length) (hs : Sound cost U c (xs.get s)) (p : Fin n) :
    GapSeparated (weight (xs.get s).equalizers p) (rankOf (xs.get s).equalizers p)
      (fun i => (cost i).real R) H := by
  intro i
  rw [snapshot_tail_gap hs p i]
  exact Clearance.separated_gap hsep s i p

theorem tracked_atoms {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (s : Fin xs.length) (p : Fin n) :
    AtomSeparated (weight (xs.get s).equalizers p) (fun i => (cost i).real R) H :=
  fun i a => Clearance.separated_atom hsep s p a i

theorem tracked_scan_correct {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (s : Fin xs.length) (hs : Sound cost U c (xs.get s)) (p : Fin n)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (C : Finset (Fin n)) :
    let out := xs.get s
    let chosen := scan out.equalizers p (fun i => (cost i).real R) H C
    PhysicalCorrect cost (out.piece p) (out.parents p) out.equalizers p (baselines out.parents)
      (fun i => (cost i).real R) H C chosen ∧
    CacheValid (measureProfile cost) (material (chosen.offer out.equalizers p (out.parents p)))
      (chosen.offer out.equalizers p (out.parents p)) := by
  refine ⟨?_,?_⟩
  · exact scan_correct cost _ _ (snapshot_parent_cache hs p) _ p _
      (snapshot_equalizers hs p) (hs.own_equalizers p).1 _ H hr hH hscale
      (tracked_atoms hsep s p) (tracked_gaps hsep s hs p) C
  · exact offer_cache_valid cost _ _ (snapshot_parent_cache hs p) _ p _
      (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

end EnvyFreeResearch.Full.Chores.Frontier
