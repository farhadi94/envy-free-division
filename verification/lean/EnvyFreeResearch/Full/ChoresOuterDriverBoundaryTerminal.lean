import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryTerminalProgram
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryAtomic
import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryExhausted

/-! Provenance through the actual terminal affine call and recursive completion.
The physical certificate is obtained from that very call by determinism. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction Population Completion QueryProgram OracleProtocol SubCoreEntry Boundary
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (p : Fin n) (t : Reveal.TerminalClass n)
  (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl t)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
    ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)
  (oldPrivate : RootId → Fin n → List (Parent n))
  (hold : PrivateCorrect (measureProfile cost) (fun root p => (xs.get (index root)).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get (index root)).piece p)
  (J : ℕ) (hcard : Fintype.card RootId ≤ J)
  (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
  (hlarge : 2*(2 : ℝ)^(n+2) ≤ H)
  (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)
  (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost) R R0)
  (hd : ∀ root q, Disjoint R (G.piece root q))
  (children : ChildPrograms n)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    CoordinateSpec (terminalCostModel cost) (children k hkpos hklt agent))
  (points : Set ℝ) (hknown : DataKnown points (fun root => xs.get (index root)) data)
  (hpriv : ∀ root q, CacheKnown points (oldPrivate root q)) (hR0 : CacheKnown points R0)
  (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
include hsound hsep hr hH hscale hclass good hprotected hold hG hcard hreserve hlarge hsmall
  hR hd hchildren hknown hpriv hR0 hzero hone

theorem terminal_finish_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle
      ((Terminal.terminalProgram data (fun root => xs.get (index root)) (fun i => (cost i).real R)
        H p t hmany).bind (fun returned => match returned with
          | none => .returned emptyAllocation
          | some (out,_) => finishClass data (fun root => xs.get (index root))
              (fun i => (cost i).real R) H p oldPrivate R0 children t hmany out)) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  obtain ⟨mid,first,second,hfirst,hsecond,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨out,tr,he,_,_,_,hparts,_,_,_,hwhole⟩ :=
    Terminal.terminal_executes data H p t hmany cost xs index c hsound R hsep hr hH hscale
      good hclass hprotected oracle hpolicy prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨hout,hscope⟩ := terminal_program_known cost xs index c hsound R H hsep hr hH hscale
    data p t hmany hclass hprotected oracle hpolicy points hknown.snapshots hzero hone prior first out _ he
  have hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p := by
    let s : Fin data.size := Classical.choice inferInstance
    have hcommon := Terminal.scan_common hsep (index (data.source s))
      (hsound (data.source s)).choose_spec p hr hH hscale (data.pending.partition.component p)
      data.pending.partition.representative t (hclass s) (hprotected.imp_right (fun h => h s))
    exact fun j hj => (data.pending.partition.mem_component p j).mp (hcommon.2.1 hj)
  have hnext : AllocationKnown (Known (Known points first) second) result ∧ Scoped (Known points first) second := by
    cases t with
    | inl pair =>
      rcases pair with ⟨A,B⟩
      exact finish_atomic_class_known data cost xs index c hsound R H hsep hr hH hscale p A B
        hclass hlabel out hparts hwhole good oldPrivate hold G hG J hcard hreserve hlarge hsmall
        R0 hR hd children hchildren (Known points first) (hknown.mono (by intro x hx; exact Or.inl hx))
        (fun root q => (hpriv root q).mono (by intro x hx; exact Or.inl hx))
        (hR0.mono (by intro x hx; exact Or.inl hx)) (Or.inl hzero) (Or.inl hone)
        hmany hout oracle hpolicy (prior++first) second result hsecond
    | inr A =>
      exact finish_exhausted_class_known data cost xs index c hsound R H hsep hr hH hscale p A
        hclass out hparts good oldPrivate hold G hG hprotected R0 hR hd children hchildren
        (Known points first) (hknown.mono (by intro x hx; exact Or.inl hx))
        (fun root q => (hpriv root q).mono (by intro x hx; exact Or.inl hx))
        (hR0.mono (by intro x hx; exact Or.inl hx)) (Or.inl hzero) (Or.inl hone)
        hmany hout oracle hpolicy (prior++first) second result hsecond
  exact ⟨by simpa only [known_append] using hnext.1,(scoped_append points first second).mpr ⟨hscope,hnext.2⟩⟩
end EnvyFreeResearch.Full.Chores.Outer
