import EnvyFreeResearch.Full.ChoresOuterLocalTerminalAtomic
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryFinish

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction Population Completion QueryProgram OracleProtocol SubCoreEntry
open Boundary
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (p : Fin n) (A : Finset (Fin n))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl (.inr A))
  (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p)
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (hparts : PartsCorrect cost
    (domains (Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative) Subtype.val out)
  (hwhole : ∃ j : A, material (out.parts j).suffixParts=
    Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
      (out.allocation.assigned j) p)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (hold : PrivateCorrect (measureProfile cost) (fun root p => (xs.get (index root)).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get (index root)).piece p)
  (J : ℕ) (hcard : Fintype.card RootId ≤ J)
  (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
  (hlarge : 2*(2 : ℝ)^(n+2) ≤ H)
  (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)

variable (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
    ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)
  (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost) R R0)
  (hd : ∀ root q, Disjoint R (G.piece root q))
  (children : ChildPrograms n)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    CoordinateSpec (terminalCostModel cost) (children k hkpos hklt agent))
  (points : Set ℝ) (hknown : DataKnown points (fun root => xs.get (index root)) data)
  (hpriv : ∀ root q, CacheKnown points (oldPrivate root q)) (hR0 : CacheKnown points R0)
  (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
include hsound hsep hr hH hscale hclass hparts good hold hG hprotected
  hR hd hchildren hknown hpriv hR0 hzero hone

/-- The real exhausted scan makes the recursive participant group proper;
actual terminal residue caches and recorded endpoints discharge the rest. -/
theorem finish_exhausted_class_known
    (hmany : Fintype.card A < Fintype.card (Fin data.size))
    (hout : RecordedKnown id points out)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle
      (finishClass data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p
        oldPrivate R0 children (.inr A) hmany out) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  have hcommon (s : Fin data.size) := Terminal.scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale (data.pending.partition.component p)
    data.pending.partition.representative (.inr A) (hclass s) (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hA : A.Nonempty ∧ A ≠ Finset.univ := ⟨⟨p,(hcommon s).1⟩,(hcommon s).2.2.1⟩
  apply finish_exhausted_known (terminalCostModel cost) data (fun root => xs.get (index root))
    (fun i => (cost i).real R) H p oldPrivate R0 children hchildren points hknown hpriv hR0
    hzero hone oracle hpolicy A hA hmany out hout
    (R ∪ privateUnion (terminalPrivateCache data (fun root => xs.get (index root)) A out oldPrivate))
  · exact Terminal.residue_cache_correct data (fun root => xs.get (index root)) (fun i => (cost i).real R)
      H A out oldPrivate cost c hsound good hparts hold G hG R R0 hR hd
  · exact hex
end EnvyFreeResearch.Full.Chores.Outer
