import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableProgramSmall

/-! Borel next-action control of the complete Snapshot ordinary-query
program, for arbitrary coded preparation results and query histories. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperQueryPrograms Chores.QueryProgram ProgramMeasurable UpperDomainDifference
variable {n k : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem from_data_program_certified
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n) (cutter : Fin k)
    (data : X → UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (UpperRepair.coarse n))
      (UpperRepair.fine n)) (zeroStart : X → UpperCircular.Circle) (smallTape : X → CandidateTape k)
    (fresh : X → UpperRepair.Tape n k) (ho : Measurable origin) (hd : Measurable data)
    (hz : Measurable zeroStart) (hst : Measurable smallTape) (hf : Measurable fresh) :
    Certified (fun x => fromDataProgram hk chores active (origin x) cutter (data x)
      (zeroStart x) (smallTape x) (fresh x)) := by
  let values (x : X) := UpperGridData.table active (origin x) (data x)
  have hv := UpperGridData.table_measurable active origin data ho hd
  have hD := selectedDistance_measurable (by omega) values cutter hv
  have haligned := UpperGridData.aligned_measurable data hd
  have hcuts := UpperGridData.cuts_measurable data hd
  have hsmall := small_program_certified (by omega) chores active _ cutter _
    (fun x e => values x (selectedRow (by omega) (values x) cutter) e-values x cutter e) _ smallTape fresh
    haligned (fun e => (measurable_pi_apply e).comp hcuts)
    (fun e => (selected_value_measurable (by omega) values cutter hv e).sub (hv cutter e)) hD hst hf
  have hrepair := program_certified (by omega) chores active (margin n) _ _ fresh
    (candidateBuffer_measurable (by omega) active origin data cutter ho hd)
    (Measurable.of_eval (fun j => candidateOld_measurable (by omega) active origin data cutter j ho hd)) hf
  have hlarge := hrepair.bind (fun z => .returned (restoreRejected (origin z.1) z.2))
    (Certified.returned _ (restoreRejected_measurable (fun z : X × PhysicalResult n k => origin z.1)
      Prod.snd (ho.comp measurable_fst) measurable_snd))
  have hzero := zero_program_certified (by omega) chores active _ cutter zeroStart haligned hz
  have hlast := Certified.branch (fun x => decide (selectedDistance (by omega) (values x) cutter < UpperRepair.nearError n / 16))
    (decide_measurable _ (measurableSet_lt hD measurable_const)) _ _ hsmall hlarge
  have hall := Certified.branch (fun x => decide (selectedDistance (by omega) (values x) cutter=0))
    (decide_measurable _ (measurableSet_eq_fun hD measurable_const)) _ _ hzero hlast
  apply hall.congr
  intro x
  simp only [fromDataProgram,values,decide_eq_true_eq,Function.comp_def]

set_option maxHeartbeats 800000 in
theorem snapshot_program_certified
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n)
    (cutter : Fin k) (tape : X → Tape n k) (ho : Measurable origin) (ht : Measurable tape) :
    Certified (fun x => snapshotProgram hk chores active (origin x) cutter (tape x)) := by
  have hprepare := UpperRecordedGridProgramMeasurable.prepare_certified active origin (UpperRepair.coarse n)
    (UpperRepair.fine n) (fun x => (tape x).1) ho (fun j => (measurable_pi_apply j).comp (measurable_fst.comp ht))
  have hrest := measurable_snd.comp ht
  have htail := measurable_snd.comp hrest
  let Data := UpperGridData.Data n (UpperRecordedQuantiles.count (Agent:=Fin k) (UpperRepair.coarse n))
    (UpperRepair.fine n)
  have hcont := from_data_program_certified (X:=X × Data) hk chores active
    (fun z => origin z.1) cutter (fun z => z.2)
    (fun z => (tape z.1).2.1) (fun z => (tape z.1).2.2.1) (fun z => (tape z.1).2.2.2)
    (ho.comp measurable_fst) measurable_snd
    ((measurable_fst.comp hrest).comp measurable_fst) ((measurable_fst.comp htail).comp measurable_fst)
    ((measurable_snd.comp htail).comp measurable_fst)
  have hfinal := hprepare.bind _ hcont
  exact hfinal


theorem snapshot_next_measurable
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n)
    (cutter : Fin k) (tape : X → Tape n k) (ho : Measurable origin) (ht : Measurable tape) :
    Measurable (fun z : X × History n =>
      ((snapshotProgram hk chores active (origin z.1) cutter (tape z.1)).after z.2).action) :=
  (snapshot_program_certified hk chores active origin cutter tape ho ht).measurable_next
end EnvyFreeResearch.Full.UpperSnapshotProtocol
