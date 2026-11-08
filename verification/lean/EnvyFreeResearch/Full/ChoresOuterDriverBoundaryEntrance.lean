import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryTerminal
import EnvyFreeResearch.Full.ChoresOuterDriverCorrect

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Population Completion ComponentRecording ComponentPayments SubCoreEntry
open Boundary
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
    CoordinateSpec cost (children k hkpos hklt agent))


  (points : Set ℝ) (hknown : DataKnown points xs.get entry.data)
  (hpriv : ∀ root q, CacheKnown points (entry.privateCache root q)) (hR0 : CacheKnown points R0)
  (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
include hsound hsep hr hH hscale hR hG hd hinv hroots hreserve hlarge hsmall hchildren
  hknown hpriv hR0 hzero hone

theorem finish_terminal_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (prior trace : History (Query (Fin n)) ℝ) (result : Allocation n (Fin n))
    (hex : Executes oracle
      (finishTerminal xs.get (fun i => (cost.measure i).real R) H R0 children entry) prior result trace) :
    AllocationKnown (Known points trace) result ∧ Scoped points trace := by
  let r := fun i => (cost.measure i).real R
  let data := entry.data.filter entry.roots
  letI : Nonempty (Fin data.size) := Terminal.cohort_nonempty entry.data xs.get entry.label r H
    entry.terminalClass entry.roots entry.choice
  let hmany := Terminal.cohort_more_roots entry.data xs.get entry.label r H entry.terminalClass entry.roots entry.choice
  have hf := Terminal.cohort_facts entry.data xs.get entry.label r H entry.terminalClass entry.roots entry.choice
  have good : data.Good xs.get cost.measure r H := Terminal.cohort_good entry.data xs.get entry.label r H
    entry.terminalClass entry.roots entry.choice cost.measure hinv.good
  have hprotected : data.pending.partition.component entry.label ≠ Finset.univ ∨
      ∀ s, c ∉ ProtectedPivot.eligible (xs.get (data.source s)) H r entry.label := by
    by_cases hC : data.pending.partition.component entry.label ≠ Finset.univ
    · exact Or.inl hC
    · exact Or.inr (fun s => (hinv.protection.terminal_entrance entry.label (entry.roots.get s)).resolve_left hC)
  exact terminal_finish_known data cost.measure xs id c hsound R H hsep hr hH hscale
    entry.label entry.terminalClass hmany hf.2.2 good hprotected entry.privateCache hinv.complement
    G hG J (by simpa only [Fintype.card_fin] using hroots) hreserve hlarge hsmall R0 hR hd
    children hchildren points (hknown.filter entry.roots) hpriv hR0 hzero hone
    oracle hpolicy prior trace result (by
      simp only [finishTerminal] at hex
      convert hex using 1
      congr 1
      funext returned
      cases returned with
      | none => rfl
      | some pair => rcases pair with ⟨out,package⟩; rfl)
end EnvyFreeResearch.Full.Chores.Outer
