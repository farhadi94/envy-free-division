import EnvyFreeResearch.Full.ChoresTerminalOffers
import EnvyFreeResearch.Full.ChoresOuterOpenGroup
import EnvyFreeResearch.Full.ChoresComponentClosedPhysicalProgram

/-! The actual affine terminal call succeeds from the immutable-table
classification. Its numerical payment hypotheses are derived internally. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Equalizers Snapshot Frontier Scheduler ComponentRecording ComponentPayments SubCore SubCorePhysical SubCoreEntry
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (p : Fin n) (t : Reveal.TerminalClass n)
  (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))

def terminalProgram :=
  ComponentClosed.program data.pending data.visited t.participants p data.packages data.frames
    (Outer.originalGaps data original) hmany (masked data original r H)

def terminalPackage (out : ComponentClosed.Result (Root := Fin data.size) t.participants) :=
  ComponentClosed.outputPackage data.pending data.visited t.participants p data.packages data.frames
    (Outer.originalGaps data original) out hmany

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl t)
  (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
    ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)

include hsound hsep hr hH hscale good hclass hprotected

theorem terminal_executes
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : ComponentClosed.Result (Root := Fin data.size) t.participants,
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (terminalProgram data (fun root => xs.get (index root))
        (fun i => (cost i).real R) H p t hmany) prior
        (some (out,terminalPackage data (fun root => xs.get (index root)) p t hmany out)) trace ∧
      (terminalPackage data (fun root => xs.get (index root)) p t hmany out).Valid ∧
      (terminalPackage data (fun root => xs.get (index root)) p t hmany out).live=none ∧
      SubCoreEntry.PhysicalCorrect (affineUtility cost
        (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
          data.pending.partition.representative)
        (offsets (Outer.originalGaps data (fun root => xs.get (index root))) data.pending.partition.representative))
        Subtype.val out.allocation ∧
      PartsCorrect cost (domains (blocks data (fun root => xs.get (index root))
        (fun i => (cost i).real R) H) data.pending.partition.representative) Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card t.participants) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card t.participants) ∧
      Masked.CacheCorrect (measureProfile cost)
        (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
          data.pending.partition.representative) out.cache ∧
      ∃ j : t.participants, material (out.parts j).suffixParts =
        blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
          (out.allocation.assigned j) p := by
  have hcommon (s : Fin data.size) := scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative t (hclass s)
    (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p := by
    intro j hj
    exact (data.pending.partition.mem_component p j).mp ((hcommon s).2.1 hj)
  exact ComponentClosed.program_correct data.pending data.visited t.participants p data.packages data.frames
    (Outer.originalGaps data (fun root => xs.get (index root))) hmany hlabel cost
    (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
    (masked data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
    (masked_correct data _ _ H cost c hsound)
    (fun s p i => by obtain ⟨U,hs⟩ := hsound (data.source s); exact Clearance.gap_nonnegative hs i p)
    ⟨p,(hcommon s).1⟩
    (fun s i hi => sub_nonneg.mpr ((hcommon s).2.2.2.1 i hi))
    good.live (Outer.active_package_valid data _ cost _ H good) good.allowed
    (fun i hi s => (hcommon s).2.2.2.2 i hi) oracle hpolicy prior

end EnvyFreeResearch.Full.Chores.Terminal
