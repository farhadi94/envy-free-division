import EnvyFreeResearch.Full.UpperSnapshotProtocolZeroPhysical
import EnvyFreeResearch.Full.UpperSnapshotSmallProgramCertified

/-! The zero-disagreement complete EF check is Borel on all coded states. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall Chores.QueryProgram ProgramMeasurable UpperDomainDifference
variable {n k : ℕ} {X : Type} [MeasurableSpace X]

theorem equalPieces_measurable (hk : 0 < k) (start : X → UpperSnapshotSmall.Circle)
    (out : X → ((Fin k → ℝ) × State n)) (hs : Measurable start) (ho : Measurable out) :
    Measurable (fun x => equalPieces hk (start x) (out x)) := by
  apply Measurable.of_eval
  intro j
  have hp (i : Fin k) : Measurable (fun x => (out x).1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp ho)
  have hb (i : Fin (k+1)) : Measurable (fun x => boundary hk (out x).1 i) :=
    boundary_measurable hk _ hp i
  have ha (i : Fin (k+1)) : Measurable (fun z : X × Component =>
      prefixAtom (equalTargets k i) (start z.1) ((out z.1).1 ⟨0,hk⟩)
        (boundary hk (out z.1).1 i) z.2) :=
    prefixAtom_measurable _ _ _ _ _ measurable_const (hs.comp measurable_fst)
      ((hp _).comp measurable_fst) ((hb i).comp measurable_fst) measurable_snd
  exact selectState_measurable _ _ (measurable_snd.comp ho)
    ((measurable_of_countable (fun p : Bool × Bool => p.1 && !p.2)).comp
      ((ha j.succ).prodMk (ha j.castSucc)))

theorem completeCheck_measurable (chores : Bool) (active : Fin k → Fin n)
    (pieces : X → Fin k → State n) (hp : Measurable pieces) :
    Measurable (fun x => completeCheck chores active (pieces x)) := by
  apply decide_measurable
  have hv (i j : Fin k) : Measurable (fun x => total (pieces x j) (active i)) :=
    total_measurable _ _ ((measurable_pi_apply j).comp hp) measurable_const
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  cases chores
  · exact measurableSet_le (hv i j) (hv i i)
  · exact measurableSet_le (hv i i) (hv i j)

theorem zeroFinish_measurable (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (start : X → UpperSnapshotSmall.Circle) (out : X → ((Fin k → ℝ) × State n))
    (hs : Measurable start) (ho : Measurable out) :
    Measurable (fun x => zeroFinish hk chores active (start x) (out x)) := by
  have hp := equalPieces_measurable hk start out hs ho
  have hempty : Measurable (fun x => (⟨[],(out x).2.history⟩ : State n)) :=
    UpperComponentAssembly.empty_measurable _ (state_history_measurable.comp (measurable_snd.comp ho))
  have haccept : Measurable (fun x => (equalPieces hk (start x) (out x),
      (⟨[],(out x).2.history⟩ : State n),false)) := hp.prodMk (hempty.prodMk measurable_const)
  have hreject : Measurable (fun x => ((fun _ : Fin k => (⟨[],(out x).2.history⟩ : State n)),(out x).2,true)) :=
    (Measurable.of_eval (fun _ => hempty)).prodMk ((measurable_snd.comp ho).prodMk measurable_const)
  exact haccept.ite (measurableSet_eq_fun (completeCheck_measurable chores active _ hp) measurable_const) hreject

theorem zero_program_certified (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (cutter : Fin k) (start : X → UpperSnapshotSmall.Circle)
    (ho : Measurable origin) (hs : Measurable start) :
    Certified (fun x => zeroProgram hk chores active (origin x) cutter (start x)) := by
  have hc := circle_program_certified (active cutter) origin (fun _ => shifts (equalTargets k)) start
    ho (fun _ => measurable_const) hs
  have hpost : Measurable (fun z : X × ((Fin k → ℝ) × State n) =>
      zeroFinish hk chores active (start z.1) z.2) :=
    zeroFinish_measurable hk chores active (fun z : X × ((Fin k → ℝ) × State n) => start z.1) Prod.snd
      (hs.comp measurable_fst) measurable_snd
  exact hc.bind (fun z => .returned (zeroFinish hk chores active (start z.1) z.2))
    (Certified.returned _ hpost)
end EnvyFreeResearch.Full.UpperSnapshotProtocol
