import EnvyFreeResearch.Full.RefinedChoresTerminalCohortFinish
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortAdmissible

/-! Both actual terminal constructors share one complete physical-domain
 completion contract and explicit child-cost allowances. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open QueryProgram Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n)) (R0 : List (Parent n))

variable (cost : Population.Costs n)
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (original root))
    (good : data.Good original cost.measure r H)
    (hparts : PartsCorrect cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (hcorrect : PhysicalCorrect (affineUtility cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation)
    (hvalid : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid)
    (hold : Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (original root).piece) data.cache oldPrivate)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length)
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hR : CacheValid (measureProfile cost.measure) R R0) (hd : ∀ root a, Disjoint R (G.piece root a))
    (hsep : Clearance.Separated (Clearance.entries xs) cost.measure H R)
    (hr : ∀ i, 0 < (cost.measure i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost.measure i).real R)
    (J : ℕ) (hroots : Fintype.card RootId ≤ J) (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (children : Population.ChildPrograms n) (Q C : ℕ → ℕ)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Population.Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k))
include hsound good hparts hcorrect hvalid hold hG horiginal hR hd hsep hr hH hscale hr_eq hroots hreserve hpolicy hchildren


variable (homitted : ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible
      (original (data.source s)) H r data.protectedLabel)
    (hwhole : ∃ j : group.terminalClass.participants, material (out.parts j).suffixParts =
      TerminalGroup.blocks data normal original r H group (out.allocation.assigned j) group.label)
    (hlarge : 2*(2 : ℝ)^(n+2) ≤ H) (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)
    (hnH : (n : ℝ)+2 ≤ H)
include homitted hwhole hlarge hsmall hnH

theorem TerminalGroup.finish_class_correct (qbound cbound : ℕ)
    (hatomic : ∀ B : Finset (Fin n), B.Nonempty → B ≠ Finset.univ →
      19*2^n*n+(Q Bᶜ.card+n*C Bᶜ.card)+(Q B.card+n*C B.card) ≤ qbound ∧
      19*2^n+C Bᶜ.card+C B.card ≤ cbound)
    (hexhausted : ∀ A : Finset (Fin n), A.Nonempty → A ≠ Finset.univ →
      Q Aᶜ.card+n*C Aᶜ.card ≤ qbound ∧ C Aᶜ.card ≤ cbound)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (TerminalGroup.finishClass data normal original r H group hr0 hH0 out oldPrivate R0 children)
      prior result trace ∧ trace.length ≤ qbound ∧ virtualCuts trace ≤ cbound ∧
      result.Sound cost.measure id (R ∪ ⋃ root, ⋃ a, G.piece root a) := by
  cases ht : group.terminalClass with
  | inl pair =>
    rcases pair with ⟨A,B⟩
    have hpa : group.terminalClass.participants = A := by rw [ht]; rfl
    have htype : group.terminalClass = .inl (group.terminalClass.participants,B) := by rw [hpa]; exact ht
    have hb := TerminalGroup.atomic_extracted_bounds data normal original r H group out cost.measure c hsound hparts
      xs index horiginal R hsep hr hH hscale hr_eq B htype hwhole
    obtain ⟨result,trace,he,hq,hc,hs⟩ := TerminalGroup.finish_atomic_correct data normal original r H group hr0 hH0
      out oldPrivate R0 cost c hsound good hparts hcorrect hvalid hold G hG xs index horiginal R hR hd
      hsep hr hH hscale hr_eq J hroots hreserve oracle hpolicy children Q C hchildren
      B hb.1 hb.2.1 htype hwhole hlarge hsmall prior
    rw [← TerminalGroup.finish_class_atomic data normal original r H group hr0 hH0 out oldPrivate R0
      B hb.1 hb.2.1 htype children] at he
    exact ⟨result,trace,he,hq.trans (hatomic B hb.1 hb.2.1).1,hc.trans (hatomic B hb.1 hb.2.1).2,hs⟩
  | inr A =>
    have hpa : group.terminalClass.participants = A := by rw [ht]; rfl
    have htype : group.terminalClass = .inr group.terminalClass.participants := by rw [hpa]; exact ht
    have ha := TerminalGroup.admissible data normal original r H group cost.measure xs index c hsound horiginal R
      hsep hr hH hscale hr_eq homitted
    obtain ⟨result,trace,he,hq,hc,hs⟩ := TerminalGroup.finish_exhausted_correct data normal original r H group hr0 hH0
      out oldPrivate R0 cost c hsound good hparts hcorrect hvalid hold G hG xs index horiginal R hR hd
      hsep hr hH hscale hr_eq J hroots hreserve oracle hpolicy children Q C hchildren
      ha.1 ha.2 htype hnH prior
    rw [← TerminalGroup.finish_class_exhausted data normal original r H group hr0 hH0 out oldPrivate R0
      ha.1 ha.2 htype children] at he
    exact ⟨result,trace,he,hq.trans (hexhausted _ ha.1 ha.2).1,hc.trans (hexhausted _ ha.1 ha.2).2,hs⟩

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.finish_class_correct
