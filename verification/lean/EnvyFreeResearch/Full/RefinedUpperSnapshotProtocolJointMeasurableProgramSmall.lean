import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolJointMeasurableSmall
import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurableCertified

/-! Actual small-branch next-action certificate, including all rejected
histories and the cache-only safety guard before the fresh Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperQueryPrograms UpperSnapshotRepetition ProtocolMeasurable
  Chores.QueryProgram ProgramMeasurable
variable {n k m : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem small_packet_finish_certified
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (cutter : Fin k)
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (D : X → ℝ) (fresh : X → RefinedUpperRepair.Tape n k) (packet : X → SmallPacket n k) (history : X → History n)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : ∀ e, Measurable (fun x => score x e)) (hD : Measurable D)
    (hf : Measurable fresh) (hp : Measurable packet) (hh : Measurable history) :
    Certified (fun x =>
      let candidate := allocationFrom (by omega) (packet x).1 (active cutter) (cuts x) (positiveIndices (score x))
        (smallAmount n k (D x)) (packet x).2.1.1 (packet x).2.1.2 (packet x).2.2.1 (packet x).2.2.2
      if candidateSafe chores active candidate.1 candidate.2.1 then
        (RefinedUpperSnapshotProtocol.program hk chores active (margin n) candidate.2.1 candidate.1 (fresh x)).bind
          (fun out => .returned (restoreRejected (origin x) out))
      else .returned (rejectWhole (origin x) (history x))) := by
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
  have hrepair := program_certified hk chores active (margin n) _ _ fresh hbuffer hold hf
  have hyes := hrepair.bind (fun z => .returned (restoreRejected (origin z.1) z.2))
    (Certified.returned _ (restoreRejected_measurable (fun z : X × PhysicalResult n k => origin z.1)
      Prod.snd (ho.comp measurable_fst) measurable_snd))
  exact Certified.branch _ (candidateSafe_measurable chores active _ _ hold hbuffer) _ _ hyes
    (Certified.returned _ (rejectWhole_measurable origin history ho hh))

set_option maxHeartbeats 800000 in
theorem small_program_certified
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : X → State n) (cutter : Fin k)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (D : X → ℝ)
    (tape : X → CandidateTape k) (fresh : X → RefinedUpperRepair.Tape n k)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : ∀ e, Measurable (fun x => score x e)) (hD : Measurable D)
    (htape : Measurable tape) (hf : Measurable fresh) :
    Certified (fun x => smallProgram hk chores active (origin x) cutter (cuts x) (score x) (D x) (tape x) (fresh x)) := by
  have ht : Measurable (fun x => smallAmount n k (D x)) :=
    (measurable_const.sub (measurable_const.mul hD)).div_const _
  have hrun₀ := actual_small_packet_varying_domain_certified hk (active cutter)
    (fun x => domain (origin x).cells) (UpperSnapshotProtocol.recorded_domain_membership_measurable _ (state_cells_measurable.comp ho))
    origin cuts score (fun x => smallAmount n k (D x)) ho hc hs ht
  have hrun := hrun₀.comp (fun x => (x,tape x)) (measurable_id.prodMk htape)
  let next (z : X × (State n × Option (SmallPacket n k))) : QProgram n (PhysicalResult n k) :=
    match z.2.2 with
    | none => .returned (rejectWhole (origin z.1) z.2.1.history)
    | some packet =>
      let candidate := allocationFrom (by omega) packet.1 (active cutter) (cuts z.1)
        (positiveIndices (score z.1)) (smallAmount n k (D z.1)) packet.2.1.1 packet.2.1.2 packet.2.2.1 packet.2.2.2
      if candidateSafe chores active candidate.1 candidate.2.1 then
        (RefinedUpperSnapshotProtocol.program hk chores active (margin n) candidate.2.1 candidate.1 (fresh z.1)).bind
          (fun out => .returned (restoreRejected (origin z.1) out))
      else .returned (rejectWhole (origin z.1) z.2.1.history)
  have hpres := small_packet_finish_certified hk chores active cutter
      (fun p : (X × (State n × Option (SmallPacket n k))) × SmallPacket n k => origin p.1.1)
      (fun p => cuts p.1.1) (fun p => score p.1.1) (fun p => D p.1.1) (fun p => fresh p.1.1)
      (fun p => p.2) (fun p => p.1.2.1.history)
      (ho.comp (measurable_fst.comp measurable_fst))
      (fun e => (hc e).comp (measurable_fst.comp measurable_fst))
      (fun e => (hs e).comp (measurable_fst.comp measurable_fst))
      (hD.comp (measurable_fst.comp measurable_fst)) (hf.comp (measurable_fst.comp measurable_fst)) measurable_snd
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have habs := Certified.returned (Query:=Query n) (Reply:=ℝ) _
    (rejectWhole_measurable (k:=k) (fun z : X × (State n × Option (SmallPacket n k)) => origin z.1)
      (fun z => z.2.1.history) (ho.comp measurable_fst)
      (state_history_measurable.comp (measurable_fst.comp measurable_snd)))
  have hcases := Certified.optionCases (fun z : X × (State n × Option (SmallPacket n k)) => z.2.2)
    (measurable_snd.comp measurable_snd) _ _ hpres habs
  have hn : Certified next := hcases.congr (by
    intro z
    dsimp only [next]
    cases z.2.2 <;> rfl)
  exact (hrun.bind next hn).congr (fun _ => rfl)
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
