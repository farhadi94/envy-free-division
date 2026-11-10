import EnvyFreeResearch.Full.RefinedChoresClosed
import EnvyFreeResearch.Full.RefinedChoresRootState
import EnvyFreeResearch.Full.ChoresTerminalScan

/-! Root-local terminal scans supply the actual closed-batch payment
hypotheses. The roots have a common terminal class but may have different
source components and different complete component partitions. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalScans
open Set MeasureTheory OracleProtocol IntervalOracle
open Chores Chores.InitialPartition Chores.OrderedUnion Chores.Snapshot Chores.Frontier
open Chores.QueryProgram Chores.ComponentRecording Chores.ComponentPayments Chores.SubCoreEntry
open ChoreComposition RefinedChoresRootState
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (original : Root → Snapshot.Output n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (components : Root → Finset (Fin n))

def offer (s : Root) : List (Parent n) := Terminal.offer (original s) p r H (components s)
def blocks (s : Root) (_a : Fin n) : Set ℝ := material (offer original p r H components s)
def cache : Masked.Cache Root n := fun s _ => offer original p r H components s

def gaps (s : Root) (a i : Fin n) : ℝ := Clearance.gap (original s) i a

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ s, ∃ U, Snapshot.Sound cost U c (original s))
include hsound

theorem cache_correct : Masked.CacheCorrect (measureProfile cost)
    (domains (blocks original p r H components) (fun _ => p)) (cache original p r H components) := by
  intro s i
  obtain ⟨U,hs⟩ := hsound s
  exact Frontier.offer_cache_valid cost _ _ (snapshot_parent_cache hs p) _ p _
    (snapshot_equalizers hs p) (hs.own_equalizers p).1 _

omit hsound in
def terminalProgram (A : Finset (Fin n)) (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (packages : Root → Package (Fin n) RootId)
    (hmany : Fintype.card A < Fintype.card Root) :=
  RefinedChoresClosed.program A p frames hpath packages (gaps original)
    (cache original p r H components) hmany

variable (xs : List (Snapshot.Output n)) (index : Root → Fin xs.length)
    (horiginal : ∀ s, original s = xs.get (index s)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (t : Reveal.TerminalClass n) (representatives : Root → Fin n → Fin n)
    (hclass : ∀ s, Reveal.classify (original s).equalizers p (fun i => (cost i).real R) H
      (components s) (representatives s) = .inl t)
    (hprotected : ∀ s, components s ≠ Finset.univ ∨
      c ∉ ProtectedPivot.eligible (original s) H (fun i => (cost i).real R) p)
include hsound horiginal hsep hr hH hscale hclass hprotected

theorem common (s : Root) :
    p ∈ t.participants ∧ t.participants ⊆ components s ∧ t.participants ≠ Finset.univ ∧
    (∀ i ∈ t.participants, gaps original s p i ≤
      (cost i).real (blocks original p (fun i => (cost i).real R) H components s p)) ∧
    (∀ i ∉ t.participants,
      (cost i).real (blocks original p (fun i => (cost i).real R) H components s p) ≤
        gaps original s p i) := by
  obtain ⟨U,hs⟩ := hsound s
  rw [horiginal s] at hs
  have h := Terminal.scan_common hsep (index s) hs p hr hH hscale
    (components s) (representatives s) t
    (by simpa only [horiginal s] using hclass s)
    (by simpa only [horiginal s] using hprotected s)
  simpa only [gaps,blocks,offer,horiginal s] using h

/-- Every numerical input condition of the actual affine terminal call is
proved from the immutable scan and clearance, without a common partition. -/
theorem terminal_executes
    (frames : Root → Frame (Fin n) RootId) (packages : Root → Package (Fin n) RootId)
    (hpath : ∀ s j, j ∈ t.participants →
      Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (hmany : Fintype.card t.participants < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s)) (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : RefinedChoresClosed.Result (Root := Root) t.participants,
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (terminalProgram original p (fun i => (cost i).real R) H components
        t.participants frames hpath packages hmany) prior
        (some (out,RefinedChoresClosed.outputPackage t.participants p frames hpath packages
          (gaps original) out hmany)) trace ∧
      (RefinedChoresClosed.outputPackage t.participants p frames hpath packages (gaps original) out hmany).Valid ∧
      (RefinedChoresClosed.outputPackage t.participants p frames hpath packages (gaps original) out hmany).live = none ∧
      PhysicalCorrect
        (affineUtility cost (domains (blocks original p (fun i => (cost i).real R) H components) (fun _ => p))
          (offsets (gaps original) (fun _ => p))) Subtype.val out.allocation ∧
      PartsCorrect cost (domains (blocks original p (fun i => (cost i).real R) H components) (fun _ => p))
        Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card t.participants) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card t.participants) ∧
      Masked.CacheCorrect (measureProfile cost)
        (domains (blocks original p (fun i => (cost i).real R) H components) (fun _ => p)) out.cache ∧
      ∃ j : t.participants, material (out.parts j).suffixParts =
        blocks original p (fun i => (cost i).real R) H components (out.allocation.assigned j) p := by
  have hcommon := common original p H components cost c hsound xs index horiginal R hsep
    hr hH hscale t representatives hclass hprotected
  let s : Root := Classical.choice inferInstance
  exact RefinedChoresClosed.program_correct t.participants p frames hpath packages (gaps original)
    cost (blocks original p (fun i => (cost i).real R) H components)
    (cache original p (fun i => (cost i).real R) H components)
    (cache_correct original p (fun i => (cost i).real R) H components cost c hsound)
    (fun s i => Clearance.gap_nonnegative (hsound s).choose_spec i p)
    ⟨p,(hcommon s).1⟩ hmany
    (fun s i hi => sub_nonneg.mpr ((hcommon s).2.2.2.1 i hi)) hlive hvalid hreflexive
    (fun i hi s => (hcommon s).2.2.2.2 i hi) oracle hpolicy prior

end EnvyFreeResearch.Full.RefinedChoresTerminalScans
#print axioms EnvyFreeResearch.Full.RefinedChoresTerminalScans.terminal_executes
