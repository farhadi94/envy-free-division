import EnvyFreeResearch.Full.ChoresTerminalOffers
import EnvyFreeResearch.Full.ChoresComponentExtraction
import EnvyFreeResearch.Full.ChoresOuterOpenGroup

/-! Actual retained donor deviations in an exhausted affine batch. These
are measured on physical complementary pieces, not nominal credits. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
open ComponentRecording ComponentPayments ComponentExtraction
open scoped Classical

variable {n : ℕ} {RootId : Type*}
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (p : Fin n) (A : Finset (Fin n))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl (.inr A))
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (hparts : PartsCorrect cost
    (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative) Subtype.val out)

include hsound hsep hr hH hscale hclass hlabel hparts

theorem actual_exhausted_donor_deviation (i : Fin n) (hi : i ∉ A) (j : A) :
    (H-(n : ℝ)/H)*(cost i).real R ≤
      (cost i).real ((xs.get (index (data.source (out.allocation.assigned j)))).piece p \
        material (out.parts j).suffixParts)-
      Equalizers.baselines (xs.get (index (data.source (out.allocation.assigned j)))).parents i := by
  have hb (s : Fin data.size) := scan_exhausted_bounds hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative A (hclass s)
  have h := terminal_deviation Subtype.val data.pending.partition.representative out cost
    (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H) hparts
    (Outer.originalGaps data (fun root => xs.get (index root)))
    (fun s q => (xs.get (index (data.source s))).piece q)
    (fun s i => Equalizers.baselines (xs.get (index (data.source s))).parents i)
    (fun s q => by
      rw [blocks_complement data (fun root => xs.get (index root)) (fun i => (cost i).real R) H cost c hsound]
      exact sdiff_subset)
    (fun s q i => gap_eq (hsound (data.source s)).choose_spec q i)
    i j H ((cost i).real R)
    (by simpa only [hlabel j j.property,Outer.originalGaps] using (hb (out.allocation.assigned j)).2.1 i hi)
    (by simpa only [hlabel j j.property,blocks,offers] using (hb (out.allocation.assigned j)).1 i)
  simpa only [hlabel j j.property] using h

end EnvyFreeResearch.Full.Chores.Terminal
