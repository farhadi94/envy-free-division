import EnvyFreeResearch.Full.UpperSnapshotRepairSelection

/-! A fresh physical Repair followed by the actual cached Snapshot margin
check. A failed check restores the old material while retaining the complete
history of all attempted queries. No extra query is issued by the check. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
  UpperQueryPrograms Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]

def finish (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (result : PhysicalResult n k) : PhysicalResult n k :=
  if passes hk chores active gamma result then result
  else (old, ⟨origin.cells, result.2.1.history⟩, true)

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (p : UpperRepair.Tape n k) : QProgram n (PhysicalResult n k) :=
  (UpperRepair.program hk chores active origin old p).bind
    (fun result => .returned (finish (by omega) chores active gamma origin old result))

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (p : UpperRepair.Tape n k) : PhysicalResult n k :=
  finish (by omega) chores active gamma origin old
    (UpperRepair.execute policy hk chores active origin old p)

theorem finish_history (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (result : PhysicalResult n k) :
    (finish hk chores active gamma origin old result).2.1.history = result.2.1.history := by
  unfold finish
  split <;> rfl

theorem finish_accepted (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (result : PhysicalResult n k) :
    (finish hk chores active gamma origin old result).2.2 = false ↔
      passes hk chores active gamma result = true := by
  unfold finish
  split
  next hp => exact iff_of_true ((passes_iff hk chores active gamma result).mp hp).1 hp
  next hp => simp only [Bool.true_eq_false, false_iff]; exact hp

theorem finish_success_eq (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (result : PhysicalResult n k)
    (hs : (finish hk chores active gamma origin old result).2.2 = false) :
    finish hk chores active gamma origin old result = result := by
  exact if_pos ((finish_accepted hk chores active gamma origin old result).mp hs)

theorem finish_rejected (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : State n) (old : Fin k → State n) (result : PhysicalResult n k)
    (hf : (finish hk chores active gamma origin old result).2.2 = true) :
    (finish hk chores active gamma origin old result).1 = old ∧
      (finish hk chores active gamma origin old result).2.1.cells = origin.cells := by
  have hp : ¬passes hk chores active gamma result = true := by
    intro hp
    have hs := (finish_accepted hk chores active gamma origin old result).mpr hp
    rw [hf] at hs
    cases hs
  simp [finish, hp]

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (hinj : Function.Injective active) (gamma : ℝ) (origin : State n) (old : Fin k → State n)
    (p : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active gamma origin old p) origin.history
      (execute policy hk chores active gamma origin old p) trace ∧
      (execute policy hk chores active gamma origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6*n*UpperRepair.fine n ∧
      (trace.map Prod.fst).countP isCut ≤ 3*UpperRepair.fine n := by
  obtain ⟨trace,he,hh,hq,hc⟩ := UpperRepair.program_cost policy hk chores active hinj origin old p
  refine ⟨trace, ?_, ?_, hq,hc⟩
  · simpa only [program, execute, List.append_nil] using he.bind
      (fun result => Program.returned (finish (by omega) chores active gamma origin old result))
      (Executes.returned _ _)
  · exact (finish_history _ _ _ _ _ _ _).trans hh

section Measurable
variable {X : Type} [MeasurableSpace X]
theorem finish_measurable (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (gamma : ℝ)
    (origin : X → State n) (old : X → Fin k → State n) (result : X → PhysicalResult n k)
    (ho : Measurable origin) (ha : Measurable old) (hr : Measurable result) :
    Measurable (fun x => finish hk chores active gamma (origin x) (old x) (result x)) := by
  have hrestore : Measurable (fun x => (⟨(origin x).cells, (result x).2.1.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (result x).2.1.history))
    exact (state_cells_measurable.comp ho).prodMk
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hr)))
  exact hr.ite (measurableSet_eq_fun (passes_measurable hk chores active gamma result hr) measurable_const)
    (ha.prodMk (hrestore.prodMk measurable_const))
end Measurable
end EnvyFreeResearch.Full.UpperSnapshotProtocol
