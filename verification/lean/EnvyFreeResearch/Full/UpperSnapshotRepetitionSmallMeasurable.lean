import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallCheck
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestoredMeasurable

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable
variable {n m J : ℕ}

theorem small_next_measurable (hJ : 2 ≤ J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ) :
    Measurable (fun p : State n × (Circle × Circle) =>
      (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t) p.1 p.2).1) := by
  have hm := secondRestored_measurable (X := State n × (Circle × Circle)) (J:=J) policy hmeas Prod.fst cutter (fun _ => cuts)
    (fun _ => positiveIndices score) t (fun p => p.2.1) (fun p => p.2.2) measurable_fst
    (fun _ => measurable_const) measurable_const (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)
  exact hm

theorem small_reject_measurable (hJ : 2 ≤ J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ) :
    Measurable (fun p : State n × (Circle × Circle) =>
      (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t) p.1 p.2).2.isNone) := by
  have hf := firstEndowment_measurable (fun p : State n × (Circle × Circle) => p.1)
    cutter (fun _ => cuts) (fun _ => positiveIndices score) (fun _ => t) measurable_fst
    (fun _ => measurable_const) measurable_const measurable_const policy hmeas (fun p => p.2.1)
    (measurable_fst.comp measurable_snd)
  have hg := secondPiece_measurable (J:=J) (by omega) policy hmeas
    (fun p : State n × (Circle × Circle) => p.1) cutter (fun _ => cuts)
    (fun _ => positiveIndices score) t (fun p => p.2.1) (fun p => p.2.2) measurable_fst
    (fun _ => measurable_const) measurable_const (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) ⟨0,by omega⟩
  have hscore := (interpolatedTotal_measurable score (cell U cuts) _
    (state_cells_measurable.comp hf)).sub
    (interpolatedTotal_measurable score (cell U cuts) _ (state_cells_measurable.comp hg))
  have hc := decide_measurable (fun p : State n × (Circle × Circle) =>
      (∑ e, |score e|)/(8*(J:ℝ)) ≤
        interpolatedTotal score (cell U cuts)
          (firstEndowment policy p.1 cutter cuts (positiveIndices score) t p.2.1).cells -
        interpolatedTotal score (cell U cuts)
          (secondPiece (J:=J) (by omega) policy p.1 cutter cuts (positiveIndices score) t p.2.1 p.2.2
            ⟨0,by omega⟩).cells)
    (measurableSet_le measurable_const hscore)
  have hn := (measurable_of_countable (fun b : Bool => !b)).comp hc
  convert hn using 1
  funext p
  have hbool (b : Bool) (out : SmallRaw n J) :
      (if b then some out else none).isNone = !b := by cases b <;> rfl
  simp only [smallStep,smallPost,interpolationCheck,firstFrom_actual,secondFrom_actual]
  exact hbool _ _

end EnvyFreeResearch.Full.UpperSnapshotRepetition
