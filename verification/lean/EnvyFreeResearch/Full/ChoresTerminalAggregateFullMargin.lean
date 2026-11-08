import EnvyFreeResearch.Full.ChoresTerminalAggregateExhausted
import EnvyFreeResearch.Full.ChoresTerminalAggregateExhaustedResidue
import EnvyFreeResearch.Full.ChoresTerminalAggregateMargin

/-! Exhaustion supplies a margin dominating the literal entire residue,
including all frozen ancestors, in the actual terminal allocation. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
open ComponentRecording ComponentPayments ComponentExtraction SubCoreEntry
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
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


variable (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hcorrect : SubCoreEntry.PhysicalCorrect
    (affineUtility cost
      (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
        data.pending.partition.representative)
      (offsets (Outer.originalGaps data (fun root => xs.get (index root)))
        data.pending.partition.representative)) Subtype.val out.allocation)
  (hmany : Fintype.card A < Fintype.card (Fin data.size))
  (hcard : Fintype.card (Fin data.size)=Fintype.card A+1)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (hold : Outer.PrivateCorrect (measureProfile cost)
    (fun root p => (xs.get (index root)).piece p) data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get (index root)).piece p)
  (J : ℕ) (hroots : Fintype.card RootId ≤ J)
  (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H) (hnH : (n : ℝ)+2 ≤ H)

include hsound hsep hr hH hscale hclass hlabel hparts good hcorrect hcard hold hG hroots hreserve hnH

theorem actual_exhausted_full_margin (i : Fin n) (hi : i ∉ A) (j : A) :
    (cost i).real (R ∪ Outer.privateUnion (Outer.terminalPrivateCache
      data (fun root => xs.get (index root)) A out oldPrivate)) ≤
      (cost i).real (material ((fullAllocation data (fun root => xs.get (index root))
        (fun k => (cost k).real R) H p (.inr A) hmany out).pieces j)) -
      (cost i).real (material ((fullAllocation data (fun root => xs.get (index root))
        (fun k => (cost k).real R) H p (.inr A) hmany out).pieces i)) := by
  have hb (s : Fin data.size) := scan_exhausted_bounds hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative A (hclass s)
  have hsmall : ∀ j : A, ∀ s i,
      (cost i).real (blocks data (fun root => xs.get (index root)) (fun k => (cost k).real R) H s
        (data.pending.partition.representative j)) ≤ (n : ℝ)*(cost i).real R/H := by
    intro j s i
    simpa only [hlabel j j.property,blocks,offers] using (hb s).1 i
  have hprotect : ∀ i ∉ A, ∀ s,
      (cost i).real (blocks data (fun root => xs.get (index root)) (fun k => (cost k).real R) H s p) ≤
        Outer.originalGaps data (fun root => xs.get (index root)) s p i := by
    intro k hk s
    have h1 : (n : ℝ)/H ≤ H := (div_le_iff₀ (by linarith : 0 < H)).mpr hscale.le
    have h2 : (n : ℝ)*(cost k).real R/H ≤ H*(cost k).real R := by
      calc
        (n : ℝ)*(cost k).real R/H = ((n : ℝ)/H)*(cost k).real R := by ring
        _ ≤ H*(cost k).real R := mul_le_mul_of_nonneg_right h1 (hr k).le
    have ht := ((hb s).1 k).trans (h2.trans ((hb s).2.1 k hk))
    simpa only [blocks,offers,Outer.originalGaps] using ht
  have hm := actual_full_allocation_donor_margin data (fun root => xs.get (index root))
    (fun k => (cost k).real R) H p (.inr A) hmany out cost c hsound good hlabel hparts
    hcorrect hprotect hcard G hG i j (fun heq => hi (heq ▸ j.property))
    ((H-(n : ℝ)/H)*(cost i).real R)
    (actual_exhausted_donor_deviation data cost xs index c hsound R H hsep hr hH hscale
      p A hclass hlabel out hparts i hi j)
  have hu := (actual_exhausted_residue_bounds data (fun root => xs.get (index root)) A out oldPrivate
    cost R H (by linarith) c hsound good hparts hold G hG hsmall J hroots i).2
  exact (exhausted_scalar_domination n J H ((cost i).real R) _ (hr i).le hnH hreserve hu).trans hm

end EnvyFreeResearch.Full.Chores.Terminal
