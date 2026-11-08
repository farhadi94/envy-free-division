import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableProgramState
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableSecond
import EnvyFreeResearch.Full.UpperSnapshotSmallProgramPost

/-! Borel next-action certification of the actual two-stage small candidate.
The continuation is checked on all raw packets, rather than only along a
particular policy's realized output. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open Chores.QueryProgram ProgramMeasurable UpperCircular UpperCircularStage UpperQueryPrograms
  UpperRecordedDomain UpperCorrectionExecution UpperStageMeasurable
variable {n m J : ℕ} {X Output : Type} [MeasurableSpace X] [MeasurableSpace Output]

theorem partition_program_joint_certified (cutter : Fin n) (origin : X → State n)
    (q : X → Fin (J+1) → I) (start : X → Circle)
    (ho : Measurable origin) (hq : ∀ j, Measurable (fun x => q x j)) (hs : Measurable start) :
    Certified (fun x => partitionProgram (origin x) cutter (q x) (start x)) :=
  circle_program_certified cutter origin (fun x => shifts (q x)) start ho
    (fun j => measurable_project.comp (hq j.castSucc)) hs

theorem first_program_joint_certified (origin : X → State n) (cutter : Fin n)
    (cuts : X → Fin (m+2) → ℝ) (selected : X → Finset (Fin (m+1)))
    (t : X → ℝ) (start : X → Circle)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : Measurable selected) (ht : Measurable t) (hstart : Measurable start) :
    Certified (fun x => firstProgram (origin x) cutter (cuts x) (selected x) (t x) (start x)) := by
  apply partition_program_joint_certified cutter _ _ start
    (firstSource_measurable origin cutter cuts selected t ho hc hs ht) _ hstart
  intro j
  fin_cases j
  · exact measurable_const
  · exact firstAmount_measurable origin cutter cuts selected t ho hc hs ht
  · exact measurable_const

theorem two_stage_program_joint_certified (origin : X → State n) (cutter : Fin n)
    (cuts : X → Fin (m+2) → ℝ) (selected : X → Finset (Fin (m+1)))
    (t : X → ℝ) (first second : X → Circle)
    (post : X → ((Fin 2 → ℝ) × State n) → ((Fin J → ℝ) × State n) → Output)
    (ho : Measurable origin) (hc : ∀ e, Measurable (fun x => cuts x e))
    (hs : Measurable selected) (ht : Measurable t) (hf : Measurable first) (hsecond : Measurable second)
    (hpost : Measurable (fun z : (X × ((Fin 2 → ℝ) × State n)) × ((Fin J → ℝ) × State n) =>
      post z.1.1 z.1.2 z.2)) :
    Certified (fun x => twoStageProgram (origin x) cutter (cuts x) (selected x)
      (t x) (first x) (second x) (post x)) := by
  have hfirst := first_program_joint_certified origin cutter cuts selected t first ho hc hs ht hf
  unfold twoStageProgram
  refine hfirst.bind (fun z =>
    (partitionProgram (remainderFrom (origin z.1) cutter (cuts z.1) (selected z.1)
      (t z.1) (first z.1) z.2) cutter (remainderTargets J (t z.1)) (second z.1)).bind
      (fun out => .returned (post z.1 z.2 out))) ?_
  have hrem := remainderFrom_joint_measurable (fun z : X × ((Fin 2 → ℝ) × State n) => origin z.1)
    cutter (fun z => cuts z.1) (fun z => selected z.1) (fun z => t z.1) (fun z => first z.1)
    (fun z => z.2) (ho.comp measurable_fst) (fun e => (hc e).comp measurable_fst)
    (hs.comp measurable_fst) (ht.comp measurable_fst) (hf.comp measurable_fst) measurable_snd
  have hpart := partition_program_joint_certified cutter _
    (fun z : X × ((Fin 2 → ℝ) × State n) => remainderTargets J (t z.1)) (fun z => second z.1)
    hrem (fun j => (remainderTargets_joint_measurable t ht j).comp measurable_fst)
    (hsecond.comp measurable_fst)
  exact hpart.bind _ (Certified.returned _ hpost)
end EnvyFreeResearch.Full.UpperSnapshotSmall
