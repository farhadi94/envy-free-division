import EnvyFreeResearch.Full.ChoresOuterLocalTerminalSeparation
import EnvyFreeResearch.Full.ChoresTerminalPhysical

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


/-- The physical measure family packaged for the native child interface. -/
def terminalCostModel : Population.Costs n := ⟨cost,fun _ => inferInstance,fun _ => inferInstance⟩

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

include hsound hsep hr hH hscale hclass hlabel hparts hwhole good hold hG hcard hreserve hlarge hsmall
  hcorrect hprotected hcohort hR hd hchildren

theorem finish_atomic_class_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (finishClass data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p
        oldPrivate R0 children (.inl (A,B)) hmany out) prior result trace ∧
      trace.length ≤ 19*2^n*n+(Q Bᶜ.card+n*C Bᶜ.card)+(Q B.card+n*C B.card) ∧
      virtualCuts trace ≤ 19*2^n+C Bᶜ.card+C B.card ∧
      result.Sound cost id (R ∪ (⋃ root, ⋃ q, G.piece root q)) := by
  let original := fun root => xs.get (index root)
  let r := fun i => (cost i).real R
  let base := Terminal.fullAllocation data original r H p (.inl (A,B)) hmany out
  let allocated := privateUnion (Terminal.updatedCache data original r H A out)
  let rem := R ∪ privateUnion (Terminal.remainingPrivate data original A out oldPrivate)
  have hb := actual_atomic_separation data cost xs index c hsound R H hsep hr hH hscale p A B
    hclass hlabel out hparts hwhole good oldPrivate hold G hG J hcard hreserve hlarge hsmall
  have hcommon (s : Fin data.size) := Terminal.scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale (data.pending.partition.component p)
    data.pending.partition.representative (.inl (A,B)) (hclass s) (hprotected.imp_right (fun h => h s))
  have hbase : base.Sound cost id allocated := Terminal.full_allocation_sound data original r H p
    (.inl (A,B)) hmany out cost c hsound good hlabel hparts hcorrect
    (fun i hi s => (hcommon s).2.2.2.2 i hi) hcohort G hG
  have hpartition := Terminal.residue_partition data original r H A out oldPrivate cost c hsound good
    hparts hold G hG R hd
  have hsplit := atomic_domain_partition data original r H A out oldPrivate cost c hsound good hparts hold G hG R hd
  have hdis : Disjoint allocated (extracted out ∪ rem) := by
    rw [hsplit.2]
    exact hpartition.1
  have hcover : allocated ∪ (extracted out ∪ rem)=R ∪ (⋃ root, ⋃ q, G.piece root q) := by
    rw [hsplit.2]
    exact hpartition.2
  obtain ⟨result,trace,he,hq,hc,hs⟩ := Population.atomic_program_correct (terminalCostModel cost)
    oracle hpolicy B hb.1 hb.2.1 base allocated (extracted out) rem hbase hdis hsplit.1
    (extractedCache out) (fullResidueCache R0 (Terminal.remainingPrivate data original A out oldPrivate))
    (atomic_extracted_cache data original r H A out cost c hsound good hparts G hG)
    (atomic_remainder_cache data original r H A out oldPrivate cost c hsound good hparts hold G hG R R0 hR hd)
    (fun i => hb.2.2.1 _ (group_embedding_mem B i))
    (fun i => hb.2.2.2 _ (Finset.mem_compl.mp (group_embedding_mem Bᶜ i)))
    children Q C hchildren prior
  refine ⟨result,trace,?_,hq,hc,?_⟩
  · simp only [finishClass,dite_eq_left (And.intro hb.1 hb.2.1)]
    exact he
  · rw [hcover] at hs
    exact hs

end EnvyFreeResearch.Full.Chores.Outer
