import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolJointMeasurableSmall

/-! Joint Borel execution of the complete concrete Snapshot dispatcher. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperQueryPrograms
variable {n k : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem fromDataExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n) (cutter : Fin k)
    (data : X → UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (RefinedUpperRepair.coarse n))
      (RefinedUpperRepair.fine n)) (zeroStart : X → UpperCircular.Circle) (smallTape : X → CandidateTape k)
    (fresh : X → RefinedUpperRepair.Tape n k) (ho : Measurable origin) (hd : Measurable data)
    (hz : Measurable zeroStart) (hst : Measurable smallTape) (hf : Measurable fresh) :
    Measurable (fun x => fromDataExecute policy hk chores active (origin x) cutter (data x)
      (zeroStart x) (smallTape x) (fresh x)) := by
  let values (x : X) := UpperGridData.table active (origin x) (data x)
  have hv := UpperGridData.table_measurable active origin data ho hd
  have hD := selectedDistance_measurable (by omega) values cutter hv
  have haligned := UpperGridData.aligned_measurable data hd
  have hcuts := UpperGridData.cuts_measurable data hd
  have hsmall := smallExecute_measurable policy hmeas (by omega) chores active _ cutter _
    (fun x e => values x (selectedRow (by omega) (values x) cutter) e-values x cutter e) _ smallTape fresh
    haligned (fun e => (measurable_pi_apply e).comp hcuts)
    (fun e => (selected_value_measurable (by omega) values cutter hv e).sub (hv cutter e)) hD hst hf
  have hlarge := restoreRejected_measurable origin _ ho
    (execute_measurable policy hmeas (by omega) chores active (margin n) _ _ fresh
      (candidateBuffer_measurable (by omega) active origin data cutter ho hd)
      (Measurable.of_eval (fun j => candidateOld_measurable (by omega) active origin data cutter j ho hd)) hf)
  exact (zeroExecute_measurable policy hmeas (by omega) chores active _ cutter zeroStart haligned hz).ite
    (measurableSet_eq_fun hD measurable_const)
    (hsmall.ite (measurableSet_lt hD measurable_const) hlarge)

theorem snapshotExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n)
    (cutter : Fin k) (tape : X → Tape n k) (ho : Measurable origin) (ht : Measurable tape) :
    Measurable (fun x => snapshotExecute policy hk chores active (origin x) cutter (tape x)) := by
  have hdata := (UpperGridMerge.prepare_measurable policy hmeas active (RefinedUpperRepair.coarse n)
    (RefinedUpperRepair.fine n)).comp (ho.prodMk (measurable_fst.comp ht))
  have hrest := measurable_snd.comp ht
  have htail := measurable_snd.comp hrest
  exact fromDataExecute_measurable policy hmeas hk chores active origin cutter _ _ _ _ ho hdata
    (measurable_fst.comp hrest) (measurable_fst.comp htail) (measurable_snd.comp htail)
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
