import EnvyFreeResearch.Full.ChoresOuterLocalTerminalExhausted
import EnvyFreeResearch.Full.ChoresOuterLocalBudget

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
  (p : Fin n) (t : Reveal.TerminalClass n)
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl t)
  (hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p)
  (out : ComponentClosed.Result (Root := Fin data.size) t.participants)
  (hparts : PartsCorrect cost
    (domains (Terminal.blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
      data.pending.partition.representative) Subtype.val out)
  (hwhole : ∃ j : t.participants, material (out.parts j).suffixParts=
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
  (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
  (hcohort : Fintype.card (Fin data.size)=Fintype.card t.participants+1)
  (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost) R R0)
  (hd : ∀ root q, Disjoint R (G.piece root q))
  (children : ChildPrograms n)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    Specification (terminalCostModel cost) agent (children k hkpos hklt agent) ((Parameters.totalCapacity k).queries+n*(Parameters.totalCapacity k).cuts) ((Parameters.totalCapacity k).cuts))


include hsound hsep hr hH hscale hclass hlabel hparts hwhole good hold hG hcard hreserve hlarge hsmall
  hcorrect hprotected hcohort hR hd hchildren

theorem finish_class_correct (hnH : (n : ℝ)+2 ≤ H)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (finishClass data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p
        oldPrivate R0 children t hmany out) prior result trace ∧
      trace.length ≤ 19*2^n*n+childQueries n ∧
      virtualCuts trace ≤ 19*2^n+childCuts n ∧
      result.Sound cost id (R ∪ (⋃ root, ⋃ q, G.piece root q)) := by
  let Q := fun k => (Parameters.totalCapacity k).queries
  let C := fun k => (Parameters.totalCapacity k).cuts
  cases t with
  | inl pair =>
    obtain ⟨A,B⟩ := pair
    have hb := actual_atomic_separation data cost xs index c hsound R H hsep hr hH hscale p A B
      hclass hlabel out hparts hwhole good oldPrivate hold G hG J hcard hreserve hlarge hsmall
    obtain ⟨result,trace,he,hq,hc,hs⟩ := finish_atomic_class_correct data cost xs index c hsound
      R H hsep hr hH hscale p A B hclass hlabel out hparts hwhole good oldPrivate hold G hG
      J hcard hreserve hlarge hsmall hcorrect hprotected hmany hcohort R0 hR hd children Q C hchildren
      oracle hpolicy prior
    have hallow := child_allowance_two (b:=Bᶜ.card) (d:=B.card)
      (Finset.card_pos.mpr (Population.complement_nonempty hb.2.1)) (Finset.card_pos.mpr hb.1)
      (by simpa only [Nat.add_comm] using Population.group_sizes B)
    refine ⟨result,trace,he,?_,?_,hs⟩
    · change trace.length ≤ 19*2^n*n+childQueries n
      dsimp only [Q,C] at hq
      omega
    · dsimp only [C] at hc
      omega
  | inr A =>
    have hcommon (s : Fin data.size) := Terminal.scan_common hsep (index (data.source s))
      (hsound (data.source s)).choose_spec p hr hH hscale (data.pending.partition.component p)
      data.pending.partition.representative (.inr A) (hclass s) (hprotected.imp_right (fun h => h s))
    let s : Fin data.size := Classical.choice inferInstance
    have ha : A.Nonempty := ⟨p,(hcommon s).1⟩
    obtain ⟨result,trace,he,hq,hc,hs⟩ := finish_exhausted_class_correct data cost xs index c hsound
      R H hsep hr hH hscale p A hclass hlabel out hparts good oldPrivate hold G hG J hcard hreserve
      hcorrect hprotected hmany hcohort R0 hR hd children Q C hchildren hnH oracle hpolicy prior
    have hallow := child_allowance_one (Population.group_card_lt (Population.complement_proper ha))
    refine ⟨result,trace,he,?_,?_,hs⟩
    · dsimp only [Q,C] at hq
      omega
    · dsimp only [C] at hc
      omega

end EnvyFreeResearch.Full.Chores.Outer
