import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableRun
import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableReturns

/-! The actual small-candidate dispatcher is jointly Borel, including
exhausted attempts, cache safety checks, fresh Repair, and full restoration. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperQueryPrograms UpperSnapshotRepetition ProtocolMeasurable
variable {n k m : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

abbrev SmallPacket (n k : ℕ) := Packet (State n) (UpperCircular.Circle × UpperCircular.Circle) (SmallRaw n k)

theorem small_packet_finish_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (cutter : Fin k)
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (D : X → ℝ) (fresh : X → UpperRepair.Tape n k) (packet : X → SmallPacket n k) (history : X → History n)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : ∀ e, Measurable (fun x => score x e)) (hD : Measurable D)
    (hf : Measurable fresh) (hp : Measurable packet) (hh : Measurable history) :
    Measurable (fun x =>
      let candidate := allocationFrom (by omega) (packet x).1 (active cutter) (cuts x) (positiveIndices (score x))
        (smallAmount n k (D x)) (packet x).2.1.1 (packet x).2.1.2 (packet x).2.2.1 (packet x).2.2.2
      if candidateSafe chores active candidate.1 candidate.2.1 then
        restoreRejected (origin x) (execute policy hk chores active (margin n) candidate.2.1 candidate.1 (fresh x))
      else rejectWhole (origin x) (history x)) := by
  let candidate (x : X) := allocationFrom (by omega) (packet x).1 (active cutter) (cuts x) (positiveIndices (score x))
    (smallAmount n k (D x)) (packet x).2.1.1 (packet x).2.1.2 (packet x).2.2.1 (packet x).2.2.2
  have ht : Measurable (fun x => smallAmount n k (D x)) :=
    (measurable_const.sub (measurable_const.mul hD)).div_const _
  have hpstart := measurable_fst.comp (measurable_snd.comp hp)
  have hpraw := measurable_snd.comp (measurable_snd.comp hp)
  have ha : Measurable candidate := allocationFrom_joint_measurable (by omega) _ (active cutter) cuts
    (fun x => positiveIndices (score x)) _ _ _ _ _ (measurable_fst.comp hp) hc
    (positiveIndices_measurable score hs) ht (measurable_fst.comp hpstart) (measurable_snd.comp hpstart)
    (measurable_fst.comp hpraw) (measurable_snd.comp hpraw)
  have hold := measurable_fst.comp ha
  have hbuffer := measurable_fst.comp (measurable_snd.comp ha)
  exact (restoreRejected_measurable origin _ ho
    (execute_measurable policy hmeas hk chores active (margin n) _ _ fresh hbuffer hold hf)).ite
      (measurableSet_eq_fun (candidateSafe_measurable chores active _ _ hold hbuffer) measurable_const)
      (rejectWhole_measurable origin history ho hh)

set_option maxHeartbeats 800000 in
theorem smallExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n) (cutter : Fin k)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (D : X → ℝ)
    (tape : X → CandidateTape k) (fresh : X → UpperRepair.Tape n k)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : ∀ e, Measurable (fun x => score x e)) (hD : Measurable D)
    (htape : Measurable tape) (hf : Measurable fresh) :
    Measurable (fun x => smallExecute policy hk chores active (origin x) cutter (cuts x) (score x) (D x) (tape x) (fresh x)) := by
  have ht : Measurable (fun x => smallAmount n k (D x)) :=
    (measurable_const.sub (measurable_const.mul hD)).div_const _
  have hrun₀ := actual_small_packet_varying_domain_measurable hk policy hmeas (active cutter)
    (fun x => domain (origin x).cells) (recorded_domain_membership_measurable _ (state_cells_measurable.comp ho))
    origin cuts score (fun x => smallAmount n k (D x)) ho hc hs ht
  have hrun := hrun₀.comp (measurable_id.prodMk htape)
  let current (x : X) := run (packetStep (smallStep policy (active cutter) (cuts x)
    (positiveIndices (score x)) (smallAmount n k (D x))
    (interpolationCheck hk (active cutter) (cuts x) (score x) (domain (origin x).cells) (smallAmount n k (D x)))))
    (drawList (tape x)) (origin x)
  have hcurrent : Measurable current := hrun
  let present (x : X) (packet : SmallPacket n k) :=
    let candidate := allocationFrom (by omega) packet.1 (active cutter) (cuts x) (positiveIndices (score x))
      (smallAmount n k (D x)) packet.2.1.1 packet.2.1.2 packet.2.2.1 packet.2.2.2
    if candidateSafe chores active candidate.1 candidate.2.1 then
      restoreRejected (origin x) (execute policy hk chores active (margin n) candidate.2.1 candidate.1 (fresh x))
    else rejectWhole (origin x) (current x).1.history
  have hpres : Measurable (fun p : X × SmallPacket n k => present p.1 p.2) :=
    small_packet_finish_measurable policy hmeas hk chores active cutter
      (fun p : X × SmallPacket n k => origin p.1) (fun p => cuts p.1) (fun p => score p.1)
      (fun p => D p.1) (fun p => fresh p.1) (fun p => p.2) (fun p => (current p.1).1.history)
      (ho.comp measurable_fst) (fun e => (hc e).comp measurable_fst)
      (fun e => (hs e).comp measurable_fst) (hD.comp measurable_fst) (hf.comp measurable_fst) measurable_snd
      ((state_history_measurable.comp (measurable_fst.comp hcurrent)).comp measurable_fst)
  have habs := rejectWhole_measurable (k:=k) origin (fun x => (current x).1.history) ho
    (state_history_measurable.comp (measurable_fst.comp hcurrent))
  have hfinal := measurable_option_cases (present:=present)
    (absent:=fun x => rejectWhole (origin x) (current x).1.history) (measurable_snd.comp hcurrent) hpres habs
  convert hfinal using 1
  funext x
  simp only [smallExecute,Function.comp_def,id_eq,present,current]
  split <;> simp_all only
end EnvyFreeResearch.Full.UpperSnapshotProtocol
