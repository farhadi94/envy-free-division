import EnvyFreeResearch.Full.ChoresTerminalPhysical

/-! Actual terminal execution followed by complete physical pool assembly.
The complete allocation of the retained domain includes frozen ancestors. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open Equalizers Snapshot Frontier Scheduler ComponentRecording ComponentPayments SubCore SubCoreEntry
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (H : ℝ) (p : Fin n) (t : Reveal.TerminalClass n)
  (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hclass : ∀ s, Reveal.classify (xs.get (index (data.source s))).equalizers p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.inl t)
  (hprotected : data.pending.partition.component p ≠ Finset.univ ∨
    ∀ s, c ∉ ProtectedPivot.eligible (xs.get (index (data.source s))) H (fun i => (cost i).real R) p)
  (hcard : Fintype.card (Fin data.size)=Fintype.card t.participants+1)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(xs.get (index root)).piece p)

include hsound hsep hr hH hscale good hclass hprotected hcard hG

theorem terminal_physical_executes
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : ComponentClosed.Result (Root := Fin data.size) t.participants,
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (terminalProgram data (fun root => xs.get (index root))
        (fun i => (cost i).real R) H p t hmany) prior
        (some (out,terminalPackage data (fun root => xs.get (index root)) p t hmany out)) trace ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card t.participants) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card t.participants) ∧
      (fullAllocation data (fun root => xs.get (index root)) (fun i => (cost i).real R) H p t hmany out).Sound
        cost id (⋃ root, ⋃ q, material (updatedCache data (fun root => xs.get (index root))
          (fun i => (cost i).real R) H t.participants out root q)) ∧
      PartsCorrect cost (domains (blocks data (fun root => xs.get (index root))
        (fun i => (cost i).real R) H) data.pending.partition.representative) Subtype.val out ∧
      SubCoreEntry.PhysicalCorrect (affineUtility cost
        (domains (blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H)
          data.pending.partition.representative)
        (offsets (Outer.originalGaps data (fun root => xs.get (index root))) data.pending.partition.representative))
        Subtype.val out.allocation ∧
      ∃ j : t.participants, material (out.parts j).suffixParts =
        blocks data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
          (out.allocation.assigned j) p := by
  obtain ⟨out,trace,hexec,hvalid,hclosed,hcorrect,hparts,hq,hc,hcache,hwhole⟩ :=
    terminal_executes data H p t hmany cost xs index c hsound R hsep hr hH hscale good hclass hprotected
      oracle hpolicy prior
  have hcommon (s : Fin data.size) := scan_common hsep (index (data.source s))
    (hsound (data.source s)).choose_spec p hr hH hscale
    (data.pending.partition.component p) data.pending.partition.representative t (hclass s)
    (hprotected.imp_right (fun h => h s))
  let s : Fin data.size := Classical.choice inferInstance
  have hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p :=
    fun j hj => (data.pending.partition.mem_component p j).mp ((hcommon s).2.1 hj)
  refine ⟨out,trace,hexec,hq,hc,?_,hparts,hcorrect,hwhole⟩
  exact full_allocation_sound data (fun root => xs.get (index root)) (fun i => (cost i).real R) H
    p t hmany out cost c hsound good hlabel hparts hcorrect
    (fun i hi s => (hcommon s).2.2.2.2 i hi) hcard G hG

end EnvyFreeResearch.Full.Chores.Terminal
