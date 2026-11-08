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
  (p : Fin n) (A B : Finset (Fin n))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl (.inl (A,B)))
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



variable (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost) R R0)
  (hd : ∀ root q, Disjoint R (G.piece root q))
  (children : ChildPrograms n)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    CoordinateSpec (terminalCostModel cost) (children k hkpos hklt agent))
  (points : Set ℝ) (hknown : DataKnown points (fun root => xs.get (index root)) data)
  (hpriv : ∀ root q, CacheKnown points (oldPrivate root q))
  (hR0 : CacheKnown points R0)
  (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)

include hsound hsep hr hH hscale hclass hlabel hparts hwhole good hold hG hcard hreserve hlarge hsmall
  hR hd hchildren hknown hpriv hR0 hzero hone

/-- Actual terminal geometry discharges every physical premise in the atomic
coordinate adapter; only the strictly smaller population coordinate IH remains. -/
theorem finish_atomic_class_known
    (hmany : Fintype.card A < Fintype.card (Fin data.size))
    (hout : RecordedKnown id points out)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle
      (finishClass data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p
        oldPrivate R0 children (.inl (A,B)) hmany out) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  have hb := actual_atomic_separation data cost xs index c hsound R H hsep hr hH hscale p A B
    hclass hlabel out hparts hwhole good oldPrivate hold G hG J hcard hreserve hlarge hsmall
  apply finish_atomic_known (terminalCostModel cost) data (fun root => xs.get (index root))
    (fun i => (cost i).real R) H p oldPrivate R0 children hchildren points hknown hpriv hR0
    hzero hone oracle hpolicy A B ⟨hb.1,hb.2.1⟩ hmany out hout (extracted out)
    (R ∪ privateUnion (Terminal.remainingPrivate data (fun root => xs.get (index root)) A out oldPrivate))
  · exact atomic_extracted_cache data (fun root => xs.get (index root)) (fun i => (cost i).real R)
      H A out cost c hsound good hparts G hG
  · exact atomic_remainder_cache data (fun root => xs.get (index root)) (fun i => (cost i).real R)
      H A out oldPrivate cost c hsound good hparts hold G hG R R0 hR hd
  · exact fun i => hb.2.2.1 _ (group_embedding_mem B i)
  · exact fun i => hb.2.2.2 _ (Finset.mem_compl.mp (group_embedding_mem Bᶜ i))
  · exact hex
end EnvyFreeResearch.Full.Chores.Outer
