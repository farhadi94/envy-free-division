import EnvyFreeResearch.Full.ChoresOuterLocalTerminalAtomic
import EnvyFreeResearch.Full.ChoresTerminalAggregateFullMargin

/-! The actual atomic terminal split satisfies the separation ratios of
the two-group recursive completion routine. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction Population Completion QueryProgram OracleProtocol SubCoreEntry
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



variable
  (hcorrect : SubCoreEntry.PhysicalCorrect
    (affineUtility cost (domains (Terminal.blocks data (fun root => xs.get (index root))
      (fun i => (cost i).real R) H) data.pending.partition.representative)
      (offsets (originalGaps data (fun root => xs.get (index root))) data.pending.partition.representative))
    Subtype.val out.allocation)
  (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
    ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)
  (hmany : Fintype.card A < Fintype.card (Fin data.size))
  (hcohort : Fintype.card (Fin data.size)=Fintype.card A+1)
  (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost) R R0)
  (hd : ∀ root q, Disjoint R (G.piece root q))
  (children : ChildPrograms n) (Q C : ℕ → ℕ)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    Specification (terminalCostModel cost) agent (children k hkpos hklt agent) (Q k+n*C k) (C k))

include hsound hsep hr hH hscale hclass hlabel hparts good hold hG hcard hreserve
  hcorrect hprotected hcohort hR hd hchildren

theorem finish_exhausted_class_correct (hnH : (n : ℝ)+2 ≤ H)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (finishClass data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p
        oldPrivate R0 children (.inr A) hmany out) prior result trace ∧
      trace.length ≤ Q Aᶜ.card+n*C Aᶜ.card ∧
      virtualCuts trace ≤ C Aᶜ.card ∧
      result.Sound cost id (R ∪ (⋃ root, ⋃ q, G.piece root q)) := by
  let original := fun root => xs.get (index root)
  let r := fun i => (cost i).real R
  let base := Terminal.fullAllocation data original r H p (.inr A) hmany out
  let allocated := privateUnion (Terminal.updatedCache data original r H A out)
  let rem := R ∪ privateUnion (terminalPrivateCache data original A out oldPrivate)
  have hcommon (s : Fin data.size) := Terminal.scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale (data.pending.partition.component p)
    data.pending.partition.representative (.inr A) (hclass s) (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hA : A.Nonempty ∧ A ≠ Finset.univ := ⟨⟨p,(hcommon s).1⟩,(hcommon s).2.2.1⟩
  have hbase : base.Sound cost id allocated := Terminal.full_allocation_sound data original r H p
    (.inr A) hmany out cost c hsound good hlabel hparts hcorrect
    (fun i hi s => (hcommon s).2.2.2.2 i hi) hcohort G hG
  have hpartition := Terminal.residue_partition data original r H A out oldPrivate cost c hsound good
    hparts hold G hG R hd
  have hcache := Terminal.residue_cache_correct data original r H A out oldPrivate cost c hsound good
    hparts hold G hG R R0 hR hd
  have hmargin : ∀ i ∉ A, ∀ j ∈ A,
      (cost i).real rem ≤ (cost i).real (material (base.pieces j)) -
        (cost i).real (material (base.pieces i)) := by
    intro i hi j hj
    exact Terminal.actual_exhausted_full_margin data cost xs index c hsound R H hsep hr hH hscale
      p A hclass hlabel out hparts good hcorrect hmany hcohort oldPrivate hold G hG J hcard hreserve hnH i hi ⟨j,hj⟩
  obtain ⟨result,trace,he,hq,hc,hs⟩ := Population.exhausted_program_correct (terminalCostModel cost)
    oracle hpolicy A hA.1 hA.2 base allocated rem hbase hpartition.1
    (fullResidueCache R0 (terminalPrivateCache data original A out oldPrivate)) hcache hmargin
    children Q C hchildren prior
  refine ⟨result,trace,?_,hq,hc,?_⟩
  · simp only [finishClass,dite_eq_left hA]
    exact he
  · rw [hpartition.2] at hs
    exact hs

end EnvyFreeResearch.Full.Chores.Outer
