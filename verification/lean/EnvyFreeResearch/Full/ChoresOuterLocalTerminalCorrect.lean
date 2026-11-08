import EnvyFreeResearch.Full.ChoresOuterLocalTerminalClass
import EnvyFreeResearch.Full.ChoresOuterDriverCorrect

/-! The actual terminal entrance is filtered once, paid by the physical
oracle program, and completed by proper recursive child populations. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Population Completion ComponentRecording ComponentPayments SubCoreEntry
open scoped Classical

variable {n : ℕ} (cost : Population.Costs n)
  (xs : List (Snapshot.Output n)) (c pivot : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (xs.get root))
  (R : Set ℝ) (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost.measure H R)
  (hr : ∀ i, 0 < (cost.measure i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost.measure) R R0)
  (G : PackageGeometry.Pieces (Fin xs.length) (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get root).piece p)
  (hd : ∀ root p, Disjoint R (G.piece root p))
  (entry : TerminalEntrance xs.get (fun i => (cost.measure i).real R) H)
  (hinv : DriverInvariant entry.data entry.privateCache xs.get cost.measure c pivot
    (fun i => (cost.measure i).real R) H)
  (J : ℕ) (hroots : xs.length ≤ J)
  (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
  (hlarge : 2*(2 : ℝ)^(n+2) ≤ H)
  (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H) (hnH : (n : ℝ)+2 ≤ H)
  (children : ChildPrograms n)
  (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
    Specification cost agent (children k hkpos hklt agent)
      ((Parameters.totalCapacity k).queries+n*(Parameters.totalCapacity k).cuts) ((Parameters.totalCapacity k).cuts))

include hsound hsep hr hH hscale hR hG hd hinv hroots hreserve hlarge hsmall hnH hchildren

theorem finish_terminal_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (finishTerminal xs.get (fun i => (cost.measure i).real R) H R0 children entry) prior result trace ∧
      trace.length ≤ ComponentRecording.budget n n+19*2^n*n+childQueries n ∧
      virtualCuts trace ≤ SubCore.sourceBudget n+19*2^n+childCuts n ∧
      result.Sound cost.measure id (R ∪ (⋃ root, ⋃ q, G.piece root q)) := by
  let r := fun i => (cost.measure i).real R
  let data := entry.data.filter entry.roots
  letI : Nonempty (Fin data.size) := Terminal.cohort_nonempty entry.data xs.get entry.label r H
    entry.terminalClass entry.roots entry.choice
  let hmany := Terminal.cohort_more_roots entry.data xs.get entry.label r H entry.terminalClass entry.roots entry.choice
  have hf := Terminal.cohort_facts entry.data xs.get entry.label r H entry.terminalClass entry.roots entry.choice
  have good : data.Good xs.get cost.measure r H := Terminal.cohort_good entry.data xs.get entry.label r H
    entry.terminalClass entry.roots entry.choice cost.measure hinv.good
  have hcohort : Fintype.card (Fin data.size)=Fintype.card entry.terminalClass.participants+1 := by
    simpa only [Fintype.card_fin,Fintype.card_coe,data,Data.filter] using hf.2.1
  have hclass := hf.2.2
  have hprotected : data.pending.partition.component entry.label ≠ Finset.univ ∨
      ∀ s, c ∉ ProtectedPivot.eligible (xs.get (data.source s)) H r entry.label := by
    by_cases hC : data.pending.partition.component entry.label ≠ Finset.univ
    · exact Or.inl hC
    · exact Or.inr (fun s => (hinv.protection.terminal_entrance entry.label (entry.roots.get s)).resolve_left hC)
  obtain ⟨out,tr0,he0,hv,hclosed,hcorrect,hparts,hq0,hc0,hcache,hwhole⟩ :=
    Terminal.terminal_executes data H entry.label entry.terminalClass hmany cost.measure xs id c hsound R
      hsep hr hH hscale good hclass hprotected oracle hpolicy prior
  have hcommon (s : Fin data.size) := Terminal.scan_common hsep (data.source s)
    (hsound (data.source s)).choose_spec entry.label hr hH hscale
    (data.pending.partition.component entry.label) data.pending.partition.representative
    entry.terminalClass (hclass s) (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hlabel : ∀ j ∈ entry.terminalClass.participants, data.pending.partition.representative j=entry.label :=
    fun j hj => (data.pending.partition.mem_component entry.label j).mp ((hcommon s).2.1 hj)
  obtain ⟨result,tr1,he1,hq1,hc1,hs⟩ := finish_class_correct data cost.measure xs id c hsound R H hsep
    hr hH hscale entry.label entry.terminalClass hclass hlabel out hparts hwhole good entry.privateCache
    hinv.complement G hG J (by simpa only [Fintype.card_fin] using hroots) hreserve hlarge hsmall
    hcorrect hprotected hmany hcohort R0 hR hd children hchildren hnH oracle hpolicy (prior++tr0)
  have hcard : Fintype.card entry.terminalClass.participants ≤ n := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ entry.terminalClass.participants
  have hq0' := hq0.trans (recorded_budget_mono n hcard)
  have hc0' := hc0.trans (source_budget_mono hcard)
  refine ⟨result,tr0++tr1,?_,?_,?_,hs⟩
  · simp only [finishTerminal]
    exact he0.bind _ he1
  · rw [List.length_append]
    omega
  · simp only [virtualCuts,List.countP_append] at hc1 ⊢
    omega

end EnvyFreeResearch.Full.Chores.Outer
