import EnvyFreeResearch.Full.RefinedChoresGroupCommit
import EnvyFreeResearch.Full.RefinedChoresDataMass

/-! One complete ordinary pool step in the original query oracle. The
post-state is constructed from the recorded physical answer, and all
invariants and query charges are derived from that execution. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.Frontier Chores.InitialPartition Chores.OrderedUnion
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)

def Group.step : Program (Query (Fin n)) ℝ (Option (Data n RootId)) :=
  (Group.program data normal original r H group).bind (fun result =>
    .returned (result.map (fun result => Group.commit data normal original r H group result.1)))

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (good : data.Good original cost r H)
include hsound horiginal hsep hr hH hscale hr_eq

theorem Group.offer_small (s : group.Root) (i : Fin n) :
    (cost i).real (Group.blocks data normal original r H group s group.label) ≤ (n:ℝ)*r i/H := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  have hs' : Snapshot.Sound cost U c (xs.get (index (data.source (group.roots s)))) :=
    by simpa only [horiginal] using hs
  have hscan := group.scan_eq s
  simp only [Data.scan,group.label_eq,group.component_eq,hr_eq,horiginal] at hscan
  have h := (Frontier.tracked_scan_correct hsep (index (data.source (group.roots s))) hs'
    group.label hr hH hscale group.component).1
  rw [hscan] at h
  simpa only [Group.blocks,Group.offers,Outcome.offer,horiginal,hr_eq] using h.2.2.2.2 i

include good

theorem Group.step_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ after : Data n RootId, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (Group.step data normal original r H group) prior (some after) trace ∧
      after.Good original cost r H ∧ after.size < data.size ∧
      after.closed = data.closed ∧ after.protectedLabel = data.protectedLabel ∧
      (data.Omitted original c r H → after.Omitted original c r H) ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card ↥group.component) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card ↥group.component) := by
  obtain ⟨out,trace,hexec,hvalid,hphysical,hparts,hqueries,hcuts,hcache⟩ :=
    Group.program_correct data normal original r H group cost xs index c hsound horiginal R
      hsep hr hH hscale hr_eq good oracle hpolicy prior
  refine ⟨Group.commit data normal original r H group out,trace,?_,?_,
    Group.commit_decreases data normal original r H group out,rfl,rfl,Group.commit_omitted data original r H (normal := normal) group out c,hqueries,hcuts⟩
  · have h := hexec.bind (fun result => .returned (result.map
      (fun result => Group.commit data normal original r H group result.1)))
      (Executes.returned _ _)
    simpa only [List.append_nil,Group.step,Option.map_some] using h
  · apply Group.commit_good data normal original r H group out cost c hsound good hparts hvalid
    · intro i
      rw [hr_eq]
      exact (hr i).le
    · linarith
    · exact Group.offer_small data normal original r H group cost xs index c hsound horiginal R
        hsep hr hH hscale hr_eq

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.step_correct
