import EnvyFreeResearch.Full.ChoresOuterPackageFacts

/-! An open component group executed from the committed scheduler state.
The program uses actual original queries; all reserve-payment hypotheses
are derived from its stored snapshots, scans and frontier invariants. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open Components ChoreComposition OracleProtocol QueryProgram
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : Components.ProposalCycle (data.pending.outgoing hall))
  (hmany : Fintype.card (ComponentBatch.Task data.pending hall cycle) < Fintype.card (Fin data.size))

def originalGaps : Fin data.size → Fin n → Fin n → ℝ :=
  fun s p i => Clearance.gap (original (data.source s)) i p

def openGroup : Program (Query (Fin n)) ℝ
    (Option (ComponentBatch.Result data.pending hall cycle × Package (Fin n) RootId)) :=
  ComponentBatch.program data.pending hall cycle data.visited data.packages data.frames
    (originalGaps data original) hmany (offeredMaskedCache data original)

def openPackage (out : ComponentBatch.Result data.pending hall cycle) : Package (Fin n) RootId :=
  ComponentBatch.outputPackage data.pending hall cycle data.visited data.packages data.frames
    (originalGaps data original) hmany out

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)

include hsound hsep hr hH hscale good

theorem open_group_executes (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : ComponentBatch.Result data.pending hall cycle, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (openGroup data (fun root => xs.get (index root)) hall cycle hmany) prior
        (some (out,openPackage data (fun root => xs.get (index root)) hall cycle hmany out)) trace ∧
      (openPackage data (fun root => xs.get (index root)) hall cycle hmany out).Valid ∧
      SubCoreEntry.PhysicalCorrect
        (SubCoreEntry.clippedUtility cost
          (ComponentPayments.domains (offeredBlocks data (fun root => xs.get (index root))) data.pending.partition.representative)
          (ComponentPayments.offsets (originalGaps data (fun root => xs.get (index root))) data.pending.partition.representative))
        Subtype.val out.allocation ∧
      ComponentRecording.PartsCorrect cost
        (ComponentPayments.domains (offeredBlocks data (fun root => xs.get (index root))) data.pending.partition.representative)
        Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card (ComponentBatch.Task data.pending hall cycle)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card (ComponentBatch.Task data.pending hall cycle)) ∧
      Masked.CacheCorrect (measureProfile cost)
        (ComponentPayments.domains (offeredBlocks data (fun root => xs.get (index root))) data.pending.partition.representative)
        out.cache := by
  apply ComponentBatch.program_correct data.pending hall cycle data.visited data.packages data.frames
    (originalGaps data (fun root => xs.get (index root))) hmany cost
    (offeredBlocks data (fun root => xs.get (index root)))
    (offeredMaskedCache data (fun root => xs.get (index root)))
    (offered_masked_cache cost xs index c hsound data)
    _ good.live (active_package_valid data _ cost _ H good) good.allowed
    _ _ _ _ _ oracle hpolicy prior
  · intro s p i
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact Clearance.gap_nonnegative hs i p
  · intro s p i
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact original_equalized cost hs (data.frames s) (good.original_frame s) p i
  · intro s p hp
    have h := (good.frontier s p).forbidden_internal
    change _ ⊆ data.pending.partition.component (data.pending.partition.representative p) at h
    simpa only [(data.pending.partition.mem_labels p).mp (data.pending.selected_subset hall cycle hp)] using h
  · intro s p hp i
    exact offered_frontier_value cost xs index c hsound R H data good s p i
  · intro p hp s i hi
    exact offered_protection cost xs index c hsound R H hsep hr hH hscale data good hall p
      (data.pending.selected_subset hall cycle hp) s i hi
  · intro s p hp i j hj
    exact offered_containment cost xs index c hsound R H hr hH data good hall p
      (data.pending.selected_subset hall cycle hp) s i j hj

end EnvyFreeResearch.Full.Chores.Outer
