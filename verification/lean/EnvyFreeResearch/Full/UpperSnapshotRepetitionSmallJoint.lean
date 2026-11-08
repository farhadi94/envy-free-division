import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallMeasurable
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableSecond
import EnvyFreeResearch.Full.UpperSnapshotSmallJointMeasurableScore
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpoints

/-! Actual candidate computations are jointly Borel in cached preparation
rows, sorted grid endpoints, target, origin state, and both fresh starts. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]

theorem positiveIndices_measurable (score : X → Fin (m+1) → ℝ)
    (hscore : ∀ e, Measurable (fun x => score x e)) :
    Measurable (fun x => positiveIndices (score x)) := by
  apply measurable_finset_iff.mpr
  intro e
  apply measurableSet_setOfPred.mp
  simpa only [positiveIndices,Finset.mem_filter,Finset.mem_univ,true_and] using
    measurableSet_lt measurable_const (hscore e)

variable (hJ : 2≤J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (U : Set ℝ) (hU : MeasurableSet U)
    (origin : X → State n) (cuts : X → Fin (m+2) → ℝ) (score : X → Fin (m+1) → ℝ)
    (t : X → ℝ) (first second : X → Circle)
    (horigin : Measurable origin) (hcuts : ∀ e,Measurable (fun x => cuts x e))
    (hscore : ∀ e,Measurable (fun x => score x e)) (ht : Measurable t)
    (hfirst : Measurable first) (hsecond : Measurable second)

include hmeas horigin hcuts hscore ht hfirst hsecond in
theorem small_next_joint_measurable :
    Measurable (fun x => (smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
      (interpolationCheck hJ cutter (cuts x) (score x) U (t x)) (origin x) (first x,second x)).1) :=
  secondRestored_joint_measurable policy hmeas origin cutter cuts (fun x => positiveIndices (score x))
    t first second horigin hcuts (positiveIndices_measurable score hscore) ht hfirst hsecond

include hmeas horigin hcuts hscore ht hfirst hsecond hU in
theorem small_check_joint_measurable :
    Measurable (fun x => interpolationCheck hJ cutter (cuts x) (score x) U (t x) (origin x) (first x,second x)
      (firstRun policy (origin x) cutter (cuts x) (positiveIndices (score x)) (t x) (first x))
      (secondRun (J:=J) policy (origin x) cutter (cuts x) (positiveIndices (score x)) (t x) (first x) (second x))) := by
  have hf := firstEndowment_measurable origin cutter cuts (fun x => positiveIndices (score x)) t
    horigin hcuts (positiveIndices_measurable score hscore) ht policy hmeas first hfirst
  have hg := secondPiece_joint_measurable (J:=J) policy hmeas origin cutter cuts (fun x => positiveIndices (score x))
    t first second horigin hcuts (positiveIndices_measurable score hscore) ht hfirst hsecond (by omega) ⟨0,by omega⟩
  have hcontrast := (interpolatedTotal_joint_measurable U hU score hscore cuts hcuts _
    (state_cells_measurable.comp hf)).sub
    (interpolatedTotal_joint_measurable U hU score hscore cuts hcuts _ (state_cells_measurable.comp hg))
  have hD : Measurable (fun x => (∑ e, |score x e|)/(8*(J:ℝ))) :=
    (Finset.measurable_sum Finset.univ (fun e _ => (hscore e).abs)).div_const _
  simp only [interpolationCheck,firstFrom_actual,secondFrom_actual]
  exact decide_measurable _ (measurableSet_le hD hcontrast)

include hmeas horigin hcuts hscore ht hfirst hsecond hU in
theorem small_reject_joint_measurable :
    Measurable (fun x => (smallStep policy cutter (cuts x) (positiveIndices (score x)) (t x)
      (interpolationCheck hJ cutter (cuts x) (score x) U (t x)) (origin x) (first x,second x)).2.isNone) := by
  have hm := (measurable_of_countable (fun b : Bool => !b)).comp
    (small_check_joint_measurable hJ policy hmeas cutter U hU origin cuts score t first second
      horigin hcuts hscore ht hfirst hsecond)
  convert hm using 1
  funext x
  have hbool (b : Bool) (out : SmallRaw n J) : (if b then some out else none).isNone = !b := by cases b <;> rfl
  simp only [smallStep,smallPost,Function.comp_def]
  exact hbool _ _

include hmeas horigin hcuts hscore ht hfirst hsecond in
theorem smallEndpoints_joint_measurable (j : Fin (2+J)) :
    Measurable (fun x => smallEndpoints policy cutter (cuts x) (positiveIndices (score x)) (t x)
      (origin x) (first x,second x) j) := by
  have hf := firstRun_measurable origin cutter cuts (fun x => positiveIndices (score x)) t
    horigin hcuts (positiveIndices_measurable score hscore) ht policy hmeas first hfirst
  have hg := secondRun_joint_measurable (J:=J) policy hmeas origin cutter cuts (fun x => positiveIndices (score x))
    t first second horigin hcuts (positiveIndices_measurable score hscore) ht hfirst hsecond
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [smallEndpoints,Fin.append_left]
    exact (measurable_pi_apply i).comp (measurable_fst.comp hf)
  · intro i
    simp only [smallEndpoints,Fin.append_right]
    exact (measurable_pi_apply i).comp (measurable_fst.comp hg)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
