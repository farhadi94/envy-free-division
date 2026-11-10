import EnvyFreeResearch.Full.RefinedChoresLocalProgram
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortDispatch

/-! The selected terminal cohort executes its affine query program and then
allocates the entire mutable domain through proper recursive children. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.ComponentRecording Chores.SubCoreEntry
open RefinedChoresData
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (cost : Population.Costs n) (original : RootId → Snapshot.Output n)
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (original root))
    (horiginal : ∀ root, original root=xs.get (index root))
    (R : Set ℝ) (r : Fin n → ℝ) (H : ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost.measure H R)
    (hr : ∀ i, 0 < (cost.measure i).real R) (hH : 1 < H) (hscale : (n:ℝ)<H*H)
    (hr_eq : r=fun i => (cost.measure i).real R)
    (R0 : List (Parent n)) (hR : CacheValid (measureProfile cost.measure) R R0)
    (G : PackageGeometry.Pieces RootId (Fin n)) (hG : ∀ root a, G.piece root a=(original root).piece a)
    (hd : ∀ root a, Disjoint R (G.piece root a))
    (entry : PhysicalTerminalEntry original r H)
    (good : entry.state.data.Good original cost.measure r H)
    (hold : Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (original root).piece)
      entry.state.data.cache entry.state.privateCache)
    (homitted : entry.state.data.Omitted original c r H)
    (J : ℕ) (hroots : Fintype.card RootId ≤ J) (hreserve : (J:ℝ)*(n:ℝ)^2 ≤ H)
    (hlarge : 2*(2:ℝ)^(n+2) ≤ H) (hsmall : (2:ℝ)^(n+2)*(n:ℝ)^2 ≤ H)
    (hnH : (n:ℝ)+2 ≤ H)
    (children : ChildPrograms n) (Q C : ℕ → ℕ)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k))
    (qbound cbound : ℕ)
    (hatomic : ∀ B : Finset (Fin n), B.Nonempty → B ≠ Finset.univ →
      19*2^n*n+(Q Bᶜ.card+n*C Bᶜ.card)+(Q B.card+n*C B.card) ≤ qbound ∧
      19*2^n+C Bᶜ.card+C B.card ≤ cbound)
    (hexhausted : ∀ A : Finset (Fin n), A.Nonempty → A ≠ Finset.univ →
      Q Aᶜ.card+n*C Aᶜ.card ≤ qbound ∧ C Aᶜ.card ≤ cbound)
include hsound horiginal hsep hr hH hscale hr_eq hR hG hd good hold homitted
  hroots hreserve hlarge hsmall hnH hchildren hatomic hexhausted

theorem finish_terminal_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle (finishTerminal original r H R0 children entry) prior result trace ∧
      trace.length ≤ ComponentRecording.budget n n+qbound ∧
      virtualCuts trace ≤ ComponentRecording.budget n n+cbound ∧
      result.Sound cost.measure id (R ∪ ⋃ root, ⋃ a, G.piece root a) := by
  have hr0 : ∀ i, 0 ≤ r i := by intro i; rw [hr_eq]; exact (hr i).le
  have hH0 : 0 < H := by linarith
  obtain ⟨out,tr0,he0,hvalid,hclosed,hcorrect,hparts,hq0,hc0,hcache,hwhole⟩ :=
    TerminalGroup.program_correct entry.state.data entry.normal original r H entry.group hr0 hH0
      cost.measure xs index c hsound horiginal R hsep hr hH hscale hr_eq homitted good oracle hpolicy prior
  obtain ⟨result,tr1,he1,hq1,hc1,hs⟩ :=
    TerminalGroup.finish_class_correct entry.state.data entry.normal original r H entry.group hr0 hH0
      out entry.state.privateCache R0 cost c hsound good hparts hcorrect hvalid hold G hG xs index
      horiginal R hR hd hsep hr hH hscale hr_eq J hroots hreserve oracle hpolicy children Q C hchildren
      homitted hwhole hlarge hsmall hnH qbound cbound hatomic hexhausted (prior++tr0)
  have hcard : Fintype.card entry.group.terminalClass.participants ≤ n := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ entry.group.terminalClass.participants
  have hq := hq0.trans (Outer.recorded_budget_mono n hcard)
  have hc : virtualCuts tr0 ≤ ComponentRecording.budget n n :=
    (show virtualCuts tr0 ≤ tr0.length from List.countP_le_length).trans hq
  refine ⟨result,tr0++tr1,?_,?_,?_,hs⟩
  · unfold finishTerminal
    rw [dite_eq_left ⟨hr0,hH0⟩]
    exact he0.bind _ he1
  · rw [List.length_append]
    omega
  · simp only [virtualCuts,List.countP_append] at hc hc1 ⊢
    omega

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.finish_terminal_correct
