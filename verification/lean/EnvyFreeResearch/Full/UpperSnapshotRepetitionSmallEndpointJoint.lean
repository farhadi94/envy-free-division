import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallJoint
import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointFamily
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointVector

noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n m J : ℕ} {X : Type} [MeasurableSpace X]

set_option maxHeartbeats 800000 in
theorem smallEndpointVector_joint_measurable
    (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy) (cutter : Fin n)
    (U : Set ℝ) (hU : MeasurableSet U) (origin : X → State n)
    (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ) (t : X → ℝ)
    (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hscore : ∀ e, Measurable (fun x => score x e)) (ht : Measurable t)
    (j : Fin ((16*J)*(2+J))) :
    Measurable (fun p : X × Tape (Circle × Circle) (16*J) =>
      smallEndpointVector hJ policy cutter (cuts p.1) (score p.1) U (t p.1) (origin p.1) p.2 j) := by
  let step (x : X) := smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
    (interpolationCheck hJ cutter (cuts x) (score x) U (t x))
  have hn : Measurable (fun p : X × (State n × (Circle × Circle)) => (step p.1 p.2.1 p.2.2).1) := by
    exact small_next_joint_measurable (X := X × (State n × (Circle × Circle))) (hJ:=hJ) (policy:=policy) (hmeas:=hmeas) (cutter:=cutter) (U:=U)
      (origin:=fun p => p.2.1) (cuts:=fun p => cuts p.1) (score:=fun p => score p.1) (t:=fun p => t p.1)
      (first:=fun p => p.2.2.1) (second:=fun p => p.2.2.2)
      (horigin:=measurable_fst.comp measurable_snd) (hcuts:=fun e => (hcuts e).comp measurable_fst)
      (hscore:=fun e => (hscore e).comp measurable_fst) (ht:=ht.comp measurable_fst)
      (hfirst:=measurable_fst.comp (measurable_snd.comp measurable_snd))
      (hsecond:=measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hr : Measurable (fun p : X × (State n × (Circle × Circle)) => (step p.1 p.2.1 p.2.2).2.isNone) := by
    exact small_reject_joint_measurable (X := X × (State n × (Circle × Circle))) (hJ:=hJ) (policy:=policy) (hmeas:=hmeas) (cutter:=cutter) (U:=U) (hU:=hU)
      (origin:=fun p => p.2.1) (cuts:=fun p => cuts p.1) (score:=fun p => score p.1) (t:=fun p => t p.1)
      (first:=fun p => p.2.2.1) (second:=fun p => p.2.2.2)
      (horigin:=measurable_fst.comp measurable_snd) (hcuts:=fun e => (hcuts e).comp measurable_fst)
      (hscore:=fun e => (hscore e).comp measurable_fst) (ht:=ht.comp measurable_fst)
      (hfirst:=measurable_fst.comp (measurable_snd.comp measurable_snd))
      (hsecond:=measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hp (i : Fin (2+J)) : Measurable (fun p : X × (State n × (Circle × Circle)) =>
      smallEndpoints policy cutter (cuts p.1) (positiveIndices (score p.1)) (t p.1) p.2.1 p.2.2 i) := by
    exact smallEndpoints_joint_measurable (X := X × (State n × (Circle × Circle))) (policy:=policy) (hmeas:=hmeas) (cutter:=cutter)
      (origin:=fun p => p.2.1) (cuts:=fun p => cuts p.1) (score:=fun p => score p.1) (t:=fun p => t p.1)
      (first:=fun p => p.2.2.1) (second:=fun p => p.2.2.2)
      (horigin:=measurable_fst.comp measurable_snd) (hcuts:=fun e => (hcuts e).comp measurable_fst)
      (hscore:=fun e => (hscore e).comp measurable_fst) (ht:=ht.comp measurable_fst)
      (hfirst:=measurable_fst.comp (measurable_snd.comp measurable_snd))
      (hsecond:=measurable_snd.comp (measurable_snd.comp measurable_snd)) i
  have hm := endpointVector_family_measurable (fun x s d => (step x s d).1)
    (fun x s d => (step x s d).2.isNone)
    (fun x => smallEndpoints policy cutter (cuts x) (positiveIndices (score x)) (t x)) hn hr hp (16*J) j
  have hcomp := hm.comp (measurable_fst.prodMk ((horigin.comp measurable_fst).prodMk measurable_snd))
  simpa only [smallEndpointVector,step,Function.comp_def] using hcomp

end EnvyFreeResearch.Full.UpperSnapshotRepetition
