import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolDataCost
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolCounts

/-! Exact original-population Snapshot cost, including coarse preparation,
all attempted two-circle candidates, and the optional fresh Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem snapshot_program_cost (policy : Policy n) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (cutter : Fin k) (tape : Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (snapshotProgram hk chores active origin cutter tape)
      origin.history (snapshotExecute policy hk chores active origin cutter tape) trace ∧
      (snapshotExecute policy hk chores active origin cutter tape).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 12*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 6*RefinedUpperRepair.fine n := by
  let data := UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
  obtain ⟨firstTrace,he,hh⟩ := UpperRecordedGridProgram.prepare_executes policy active origin
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
  obtain ⟨tail,ht,hth,htq,htc⟩ := fromData_program_cost policy hk chores active hinj origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2
  change data.2.2.history = origin.history ++ firstTrace at hh
  have hq := UpperGridMerge.query_bound policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
  have hc := UpperGridMerge.cut_bound policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
  change data.2.2.history.length ≤ _ at hq
  change (data.2.2.history.map Prod.fst).countP isCut ≤ _ at hc
  rw [hh,List.length_append] at hq
  rw [hh,List.map_append,List.countP_append] at hc
  simp only [Fintype.card_fin] at hq hc
  have hq0 : firstTrace.length ≤ (k*RefinedUpperRepair.coarse n+RefinedUpperRepair.fine n)*(n+1) := by omega
  have hc0 : (firstTrace.map Prod.fst).countP isCut ≤ k*RefinedUpperRepair.coarse n+RefinedUpperRepair.fine n := by omega
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  have hn : 1 ≤ n := by omega
  have hcoarse : k*RefinedUpperRepair.coarse n ≤ RefinedUpperRepair.fine n := by
    have h := (RefinedUpperParameterCounts.original_count_facts n k (by omega) hkn).1
    change k*RefinedUpperParameterCounts.coarseCount _ _ ≤ RefinedUpperParameterCounts.samples _ _
    omega
  have hsmall := small_endpoints_fit (by omega : 2≤k) hkn
  have hgridq := Nat.mul_le_mul_right (n+1) (Nat.add_le_add_right hcoarse (RefinedUpperRepair.fine n))
  have hsmallq := Nat.mul_le_mul_right (n+1) hsmall
  have hnscale := Nat.mul_le_mul_right (RefinedUpperRepair.fine n) hn
  refine ⟨firstTrace++tail,?_,?_,?_,?_⟩
  · rw [hh] at ht
    exact he.bind (fun data => fromDataProgram hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2) ht
  · change (fromDataExecute policy hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2).2.1.history = _
    rw [hth,hh,List.append_assoc]
  · rw [List.length_append]
    nlinarith
  · rw [List.map_append,List.countP_append]
    omega
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
