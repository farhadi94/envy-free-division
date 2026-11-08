import EnvyFreeResearch.Full.UpperSnapshotProtocolJointMeasurablePost
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallJoint
import EnvyFreeResearch.Full.UpperSnapshotRepetitionRunFamily

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n m J : ℕ} {X : Type} [MeasurableSpace X]

theorem small_step_varying_domain_measurable
    (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy) (cutter : Fin n)
    (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1})
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (horigin : Measurable origin) (hcuts : ∀ e,Measurable (fun x => cuts x e))
    (hscore : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hfirst : Measurable first) (hsecond : Measurable second) :
    Measurable (fun x => smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
      (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x)) (origin x) (first x,second x)) := by

  have hf := firstRun_measurable origin cutter cuts (fun x => positiveIndices (score x)) t horigin hcuts
    (positiveIndices_measurable score hscore) ht policy hmeas first hfirst
  have hg := secondRun_joint_measurable (J:=J) policy hmeas origin cutter cuts (fun x => positiveIndices (score x))
    t first second horigin hcuts (positiveIndices_measurable score hscore) ht hfirst hsecond
  exact smallPost_varying_domain_measurable hJ cutter U hU origin cuts score t first second _ _
    horigin hcuts hscore ht hfirst hsecond hf hg

set_option maxHeartbeats 800000 in
theorem actual_small_packet_varying_domain_measurable
    (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy) (cutter : Fin n)
    (U : X → Set ℝ) (hU : MeasurableSet {p : X × ℝ | p.2 ∈ U p.1}) (origin : X → State n)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (t : X → ℝ)
    (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hscore : ∀ e, Measurable (fun x => score x e)) (ht : Measurable t) :
    Measurable (fun p : X × Tape (Circle × Circle) (16*J) =>
      run (packetStep (smallStep policy cutter (cuts p.1) (positiveIndices (score p.1)) (t p.1)
        (interpolationCheck hJ cutter (cuts p.1) (score p.1) (U p.1) (t p.1)))) (drawList p.2) (origin p.1)) := by
  let step (x : X) := smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
    (interpolationCheck hJ cutter (cuts x) (score x) (U x) (t x))
  have hs : Measurable (fun p : X × (State n × (Circle × Circle)) => step p.1 p.2.1 p.2.2) := by
    exact small_step_varying_domain_measurable (X := X × (State n × (Circle × Circle))) (hJ:=hJ) (policy:=policy) (hmeas:=hmeas) (cutter:=cutter) (U:=fun p => U p.1)
      (hU:=hU.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (origin:=fun p => p.2.1) (cuts:=fun p => cuts p.1) (score:=fun p => score p.1) (t:=fun p => t p.1)
      (first:=fun p => p.2.2.1) (second:=fun p => p.2.2.2)
      (horigin:=measurable_fst.comp measurable_snd) (hcuts:=fun e => (hcuts e).comp measurable_fst)
      (hscore:=fun e => (hscore e).comp measurable_fst) (ht:=ht.comp measurable_fst)
      (hfirst:=measurable_fst.comp (measurable_snd.comp measurable_snd))
      (hsecond:=measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hm := run_family_measurable (X:=X) (State:=State n) (Draw:=Circle × Circle)
    (Output:=Packet (State n) (Circle × Circle) (SmallRaw n J))
    (fun x => packetStep (step x)) (packetStep_family_measurable step hs) (16*J)
  have hcomp := hm.comp (measurable_fst.prodMk ((horigin.comp measurable_fst).prodMk measurable_snd))
  simpa only [step,Function.comp_def] using hcomp

end EnvyFreeResearch.Full.UpperSnapshotRepetition
