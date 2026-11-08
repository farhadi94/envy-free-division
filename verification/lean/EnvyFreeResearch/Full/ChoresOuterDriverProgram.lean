import EnvyFreeResearch.Full.ChoresOuterDriverTransitions
import EnvyFreeResearch.Full.ChoresOuterPrivateBatch

/-! The actual bounded outer query program. It scans cached tables, executes
old-pool batches at the real query history, and carries physical private
complement caches until the chosen terminal cohort is returned. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical
variable {n : ℕ} {RootId : Type*}

structure TerminalEntrance (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) where
  data : Data n RootId
  privateCache : RootId → Fin n → List (Parent n)
  label : Fin n
  representative : label ∈ data.pending.partition.labels
  fresh : label ∉ data.pending.pending
  terminalClass : Reveal.TerminalClass n
  roots : List (Fin data.size)
  choice : revelationChoice data original label r H=.terminal terminalClass roots

def driverProgram [NeZero n] (original : RootId → Snapshot.Output n)
    (pivot : Fin n) (r : Fin n → ℝ) (H : ℝ) :
    ℕ → (data : Data n RootId) → (RootId → Fin n → List (Parent n)) →
      Program (Query (Fin n)) ℝ (Option (TerminalEntrance original r H))
  | 0, _, _ => .returned none
  | fuel+1, data, privateCache =>
    match nextAction data with
    | .reveal p hp hf =>
      match hc : revelationChoice data original p r H with
      | .terminal t roots => .returned (some ⟨data,privateCache,p,hp,hf,t,roots,hc⟩)
      | .outside target roots =>
        match outsideCommit data original p hp r H roots target with
        | none => .returned none
        | some updated => driverProgram original pivot r H fuel updated privateCache
    | .merge hall cycle =>
      (batchProgram data hall cycle original (cohorts data hall cycle)).bind (fun results =>
        match results with
        | none => .returned none
        | some outputs =>
          let hs : (data.pending.selected hall cycle).Nonempty :=
            Finset.card_pos.mp (by have := data.pending.selected_two hall cycle; omega)
          let keep := Partition.keepLabel pivot (data.pending.selected hall cycle) hs
          let hk := Partition.keepLabel_mem pivot (data.pending.selected hall cycle) hs
          driverProgram original pivot r H fuel
            (commitBatch data hall cycle original outputs keep hk)
            (batchPrivateCache data hall cycle original privateCache outputs))

end EnvyFreeResearch.Full.Chores.Outer
