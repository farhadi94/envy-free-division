import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallJoint
import EnvyFreeResearch.Full.UpperSnapshotRepetitionRunFamily

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open ProtocolMeasurable UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n m J : ℕ} {X : Type} [MeasurableSpace X]

theorem small_step_joint_measurable
    (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy) (cutter : Fin n)
    (U : Set ℝ) (hU : MeasurableSet U)
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (horigin : Measurable origin) (hcuts : ∀ e,Measurable (fun x => cuts x e))
    (hscore : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hfirst : Measurable first) (hsecond : Measurable second) :
    Measurable (fun x => smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
      (interpolationCheck hJ cutter (cuts x) (score x) U (t x)) (origin x) (first x,second x)) := by
  have hn := small_next_joint_measurable hJ policy hmeas cutter U origin cuts score t first second
    horigin hcuts hscore ht hfirst hsecond
  have hc := small_check_joint_measurable hJ policy hmeas cutter U hU origin cuts score t first second
    horigin hcuts hscore ht hfirst hsecond
  have hf := firstRun_measurable origin cutter cuts (fun x => positiveIndices (score x)) t horigin hcuts
    (positiveIndices_measurable score hscore) ht policy hmeas first hfirst
  have hg := secondRun_joint_measurable (J:=J) policy hmeas origin cutter cuts (fun x => positiveIndices (score x))
    t first second horigin hcuts (positiveIndices_measurable score hscore) ht hfirst hsecond
  exact hn.prodMk ((measurable_some.comp (hf.prodMk hg)).ite
    (measurableSet_eq_fun hc measurable_const) measurable_const)

set_option maxHeartbeats 800000 in
theorem actual_small_packet_joint_measurable
    (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy) (cutter : Fin n)
    (U : Set ℝ) (hU : MeasurableSet U) (origin : X → State n)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (t : X → ℝ)
    (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hscore : ∀ e, Measurable (fun x => score x e)) (ht : Measurable t) :
    Measurable (fun p : X × Tape (Circle × Circle) (16*J) =>
      run (packetStep (smallStep policy cutter (cuts p.1) (positiveIndices (score p.1)) (t p.1)
        (interpolationCheck hJ cutter (cuts p.1) (score p.1) U (t p.1)))) (drawList p.2) (origin p.1)) := by
  let step (x : X) := smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
    (interpolationCheck hJ cutter (cuts x) (score x) U (t x))
  have hs : Measurable (fun p : X × (State n × (Circle × Circle)) => step p.1 p.2.1 p.2.2) := by
    exact small_step_joint_measurable (X := X × (State n × (Circle × Circle))) (hJ:=hJ) (policy:=policy) (hmeas:=hmeas) (cutter:=cutter) (U:=U) (hU:=hU)
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
