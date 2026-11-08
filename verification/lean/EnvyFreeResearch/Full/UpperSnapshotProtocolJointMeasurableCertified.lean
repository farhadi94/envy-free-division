import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurablePost
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallPostMeasurable
import EnvyFreeResearch.Full.UpperSnapshotRepetitionProgramCertified
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableProgram

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable ProgramMeasurable UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable
variable {n m J : ℕ} {X : Type} [MeasurableSpace X]

set_option maxHeartbeats 800000 in
theorem small_attempt_varying_domain_certified
    (hJ : 2≤J) (cutter : Fin n) (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (ho : Measurable origin) (hc : ∀ e,Measurable (fun x => cuts x e))
    (hs : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hf : Measurable first) (hg : Measurable second) :
    Certified (fun x => smallAttempt cutter (cuts x) (positiveIndices (score x)) (t x)
      (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x)) (origin x) (first x,second x)) := by
  have hproj : Measurable (fun p : (X × ((Fin 2 → ℝ) × State n)) × ((Fin J → ℝ) × State n) => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hpost := smallPost_varying_domain_measurable (X := (X × ((Fin 2 → ℝ) × State n)) × ((Fin J → ℝ) × State n))
    hJ cutter (fun p => U p.1.1) (hU.preimage ((hproj.comp measurable_fst).prodMk measurable_snd)) (fun p => origin p.1.1) (fun p => cuts p.1.1) (fun p => score p.1.1)
    (fun p => t p.1.1) (fun p => first p.1.1) (fun p => second p.1.1)
    (fun p => p.1.2) Prod.snd (ho.comp hproj) (fun e => (hc e).comp hproj)
    (fun e => (hs e).comp hproj) (ht.comp hproj) (hf.comp hproj) (hg.comp hproj)
    (measurable_snd.comp measurable_fst) measurable_snd
  exact two_stage_program_joint_certified origin cutter cuts (fun x => positiveIndices (score x)) t first second
    (fun x => smallPost (origin x) (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x) (origin x) (first x,second x)))
    ho hc (positiveIndices_measurable score hs) ht hf hg hpost

set_option maxHeartbeats 800000 in
theorem actual_small_packet_varying_domain_certified
    (hJ : 2≤J) (cutter : Fin n) (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1}) (origin : X → State n)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (t : X → ℝ)
    (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hscore : ∀ e, Measurable (fun x => score x e)) (ht : Measurable t) :
    Certified (fun p : X × Tape (Circle × Circle) (16*J) =>
      program (packetAttempt (smallAttempt cutter (cuts p.1) (positiveIndices (score p.1)) (t p.1)
        (interpolationCheck hJ cutter (cuts p.1) (score p.1) (U p.1) (t p.1)))) (drawList p.2) (origin p.1)) := by
  let attempt (x : X) := smallAttempt cutter (cuts x) (positiveIndices (score x)) (t x)
    (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x))
  have ha : Certified (fun p : X × (State n × (Circle × Circle)) => attempt p.1 p.2.1 p.2.2) := by
    exact small_attempt_varying_domain_certified (X := X × (State n × (Circle × Circle)))
      (hJ:=hJ) (cutter:=cutter) (U:=fun p => U p.1)
      (hU:=hU.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (origin:=fun p => p.2.1) (cuts:=fun p => cuts p.1) (score:=fun p => score p.1) (t:=fun p => t p.1)
      (first:=fun p => p.2.2.1) (second:=fun p => p.2.2.2)
      (ho:=measurable_fst.comp measurable_snd) (hc:=fun e => (hcuts e).comp measurable_fst)
      (hs:=fun e => (hscore e).comp measurable_fst) (ht:=ht.comp measurable_fst)
      (hf:=measurable_fst.comp (measurable_snd.comp measurable_snd))
      (hg:=measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hp := program_family_certified (X:=X) (State:=State n) (Draw:=Circle × Circle)
    (Output:=Packet (State n) (Circle × Circle) (SmallRaw n J))
    (fun x => packetAttempt (attempt x)) (packetAttempt_family_certified attempt ha) (16*J)
  have hcomp := hp.comp (fun p : X × Tape (Circle × Circle) (16*J) => (p.1,(origin p.1,p.2)))
    (measurable_fst.prodMk ((horigin.comp measurable_fst).prodMk measurable_snd))
  simpa only [attempt] using hcomp

end EnvyFreeResearch.Full.UpperSnapshotRepetition
