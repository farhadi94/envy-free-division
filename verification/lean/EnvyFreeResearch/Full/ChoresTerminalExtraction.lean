import EnvyFreeResearch.Full.ChoresTerminalOffers
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! Atomic extraction bounds for the actual recorded affine output.
The extracted domain is the union of complete assigned suffixes, including
zero-credit assignments; its large-mask and small-mask bounds follow from
the immutable-table scans and an actual retained whole-parent witness. -/
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
  (p : Fin n) (A B : Finset (Fin n))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl (.inl (A,B)))
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (hparts : PartsCorrect cost
    (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative) Subtype.val out)
  (hwhole : ∃ j : A, material (out.parts j).suffixParts=
    blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
      (out.allocation.assigned j) p)

include hsound hsep hr hH hscale hclass hlabel hparts hwhole

theorem actual_atomic_extracted_bounds :
    B.Nonempty ∧ B ≠ Finset.univ ∧
    (∀ i ∈ B, H*(cost i).real R ≤ (cost i).real (extracted out)) ∧
    (∀ i, i ∉ B → (cost i).real (extracted out) ≤ (n : ℝ)^2*(cost i).real R/H) := by
  have hb (s : Fin data.size) := scan_atomic_bounds hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative A B (hclass s)
  let s : Fin data.size := Classical.choice inferInstance
  refine ⟨(hb s).1,(hb s).2.1,?_,?_⟩
  · intro i hi
    apply extracted_large Subtype.val data.pending.partition.representative out cost
      (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      i H ((cost i).real R)
      (fun s => atom (xs.get (index (data.source s))) p (fun i => (cost i).real R) H
        (data.pending.partition.component p))
    · intro s
      exact (hb s).2.2.2.1 i hi
    · intro j
      rw [hlabel j j.property]
      exact (hb (out.allocation.assigned j)).2.2.1
    · obtain ⟨j,hj⟩ := hwhole
      exact ⟨j,by simpa only [hlabel j j.property] using hj⟩
  · intro i hi
    apply extracted_small Subtype.val data.pending.partition.representative out cost
      (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      hparts i H ((cost i).real R) (by linarith) (hr i).le
    · simpa only [Fintype.card_coe, Fintype.card_fin] using (Finset.card_le_univ A)
    · intro j
      rw [hlabel j j.property]
      exact (hb (out.allocation.assigned j)).2.2.2.2 i hi

end EnvyFreeResearch.Full.Chores.Terminal
