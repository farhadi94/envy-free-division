import EnvyFreeResearch.Full.RefinedChoresLocalProgram
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortProgramBoundary
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortFinishBoundary

/-! Provenance of the complete terminal affine call followed by recursive
 completion. Its physical certificates come from that same actual execution. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresLocal
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition
open Chores.OrderedUnion Chores.QueryProgram Chores.Population Chores.ComponentRecording Chores.SubCoreEntry Chores.Boundary
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
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (hcache : ∀ root a, CacheKnown points (entry.state.data.cache root a))
    (hpriv : ∀ root a, CacheKnown points (entry.state.privateCache root a))
    (hR0 : CacheKnown points R0) (hzero : (0:ℝ) ∈ points) (hone : (1:ℝ) ∈ points)
include hsound horiginal hsep hr hH hscale hr_eq hR hG hd good hold homitted
  hroots hreserve hlarge hsmall hchildren hknown hcache hpriv hR0 hzero hone

theorem finish_terminal_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Completion.Allocation n (Fin n))
    (hex : Executes oracle (finishTerminal original r H R0 children entry) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  have hr0 : ∀ i, 0 ≤ r i := by intro i; rw [hr_eq]; exact (hr i).le
  have hH0 : 0 < H := by linarith
  unfold finishTerminal at hex
  rw [dite_eq_left ⟨hr0,hH0⟩] at hex
  obtain ⟨mid,first,second,hfirst,hsecond,rfl⟩ := Executes.split_bind _ _ hex
  obtain ⟨out,tr,he,hvalid,hclosed,hcorrect,hparts,hq,hc,hrecorded,hwhole⟩ :=
    TerminalGroup.program_correct entry.state.data entry.normal original r H entry.group hr0 hH0
      cost.measure xs index c hsound horiginal R hsep hr hH hscale hr_eq homitted good oracle hpolicy prior
  obtain ⟨rfl,rfl⟩ := hfirst.deterministic he
  obtain ⟨hout,hscope⟩ := TerminalGroup.program_known entry.state.data entry.normal original r H entry.group hr0 hH0
    points hknown cost.measure xs index c hsound horiginal R hsep hr hH hscale hr_eq homitted hzero hone
    oracle hpolicy prior out _ first he
  have hnext := TerminalGroup.finish_class_known entry.state.data entry.normal original r H entry.group hr0 hH0
    out entry.state.privateCache R0 cost c hsound good hparts hold G hG xs index horiginal R hR hd hsep hr hH hscale
    hr_eq J hroots hreserve oracle hpolicy children hchildren (Known points first)
    (fun root => (hknown root).mono subset_union_left)
    (fun root a => (hcache root a).mono subset_union_left)
    (fun root a => (hpriv root a).mono subset_union_left)
    (hR0.mono subset_union_left) hout (Or.inl hzero) (Or.inl hone) homitted hwhole hlarge hsmall
    (prior++first) second result hsecond
  exact ⟨by simpa only [known_append] using hnext.1,(scoped_append points first second).mpr ⟨hscope,hnext.2⟩⟩

end EnvyFreeResearch.Full.RefinedChoresLocal
#print axioms EnvyFreeResearch.Full.RefinedChoresLocal.finish_terminal_known
