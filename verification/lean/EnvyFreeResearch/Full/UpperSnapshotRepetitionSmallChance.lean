import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallCheck
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondInvariant

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells Chores
variable {n m J : ℕ}

def smallValid (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] (U : Set ℝ) (cuts : Fin (m+2) → ℝ) (s : State n) : Prop :=
  WellFormed μ s ∧ domain s.cells=U ∧ ∀ e, SeparatedAt (cuts e) s.cells

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (cutter : Fin n) (U : Set ℝ) (hpositive : 0 < (μ cutter).real U)
  (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hlast : cuts (Fin.last (m+1))=1)
  (hmono : Monotone cuts) (score : Fin (m+1) → ℝ)
  (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hJ : 2≤J)

include hpolicy hpositive hzero hmono ht hhalf
theorem small_valid_preserved (origin : State n) (hs : smallValid μ U cuts origin)
    (z : Circle × Circle) :
    smallValid μ U cuts
      (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t) origin z).1 := by
  have hp : 0 < (μ cutter).real (domain origin.cells) := by rw [hs.2.1]; exact hpositive
  change smallValid μ U cuts (secondRestored (J:=J) policy origin cutter cuts (positiveIndices score) t z.1 z.2)
  refine ⟨secondRestored_wellFormed μ policy hpolicy origin hs.1 cutter hp cuts hzero hmono hs.2.2
    (positiveIndices score) t ht (by linarith) z.1 z.2,?_,?_⟩
  · exact (secondRestored_domain policy origin cutter cuts (positiveIndices score) t z.1 z.2).trans hs.2.1
  · intro e
    exact secondRestored_separated policy origin cutter cuts (positiveIndices score) t z.1 z.2 _ (hs.2.2 e)

theorem small_check_physical (origin : State n) (hs : smallValid μ U cuts origin)
    (z : Circle × Circle) :
    interpolationCheck hJ cutter cuts score U t origin z
      (firstRun policy origin cutter cuts (positiveIndices score) t z.1)
      (secondRun (J:=J) policy origin cutter cuts (positiveIndices score) t z.1 z.2) =
      decide ((∑ e, |score e|)/(8*(J:ℝ)) ≤ candidateContrast hJ policy origin cutter cuts
        (positiveIndices score) t (signedEstimate score (cell U cuts)) z) := by
  have hp : 0 < (μ cutter).real (domain origin.cells) := by rw [hs.2.1]; exact hpositive
  have hsupply := firstSource_positive μ origin hs.1 cutter hp cuts (positiveIndices score) t ht (by linarith)
  apply interpolationCheck_actual
  · exact (first_partition μ policy hpolicy origin hs.1 cutter cuts (positiveIndices score) t hsupply z.1).1.2.1
  · exact (second_piece_wellFormed μ policy hpolicy origin hs.1 cutter hp cuts hzero hmono hs.2.2
      (positiveIndices score) t ht (by linarith) (J:=J) (by omega) z.1 z.2 ⟨0,by omega⟩).2.1

include hlast
theorem small_failure_bound (hmeas : UpperStageMeasurable.MeasurablePolicy policy)
    (hfit : (J:ℝ)*t<1) (htlower : 1/(2*(J:ℝ))≤t)
    (hsum : ∑ e, score e=0) (hnull : ∀ e, volume (cell U cuts e)=0 → score e=0)
    (hD : 0<∑ e, |score e|) (origin : State n) (hs : smallValid μ U cuts origin) :
    (volume.prod volume) {z : Circle × Circle |
      (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t) origin z).2=none} ≤
      ENNReal.ofReal (1-1/(8*(J:ℝ))) := by
  have hp : 0 < (μ cutter).real (domain origin.cells) := by rw [hs.2.1]; exact hpositive
  have hc := actual_witness_chance μ policy hpolicy hmeas origin hs.1 cutter hp cuts hzero hlast hmono hs.2.2
    t ht hhalf hJ hfit htlower score hsum (by simpa only [hs.2.1] using hnull) hD
  rw [hs.2.1] at hc
  let E : Set (Circle × Circle) := {z | (∑ e, |score e|)/(8*(J:ℝ)) ≤
    candidateContrast hJ policy origin cutter cuts (positiveIndices score) t
      (signedEstimate score (cell U cuts)) z}
  have hm := candidate_scores_measurable μ policy hpolicy hmeas origin hs.1 cutter hp cuts hzero hmono hs.2.2
    (positiveIndices score) t ht (by linarith) hJ score (cell U cuts)
  have hE : MeasurableSet E := measurableSet_le measurable_const (hm.1.sub hm.2)
  have heq : {z : Circle × Circle |
      (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t) origin z).2=none}=Eᶜ := by
    ext z
    have hh := small_check_physical μ policy hpolicy cutter U hpositive cuts hzero hmono score t ht hhalf hJ origin hs z
    by_cases hz : z ∈ E
    · have hz' : (∑ e, |score e|)/(8*(J:ℝ)) ≤ candidateContrast hJ policy origin cutter cuts
        (positiveIndices score) t (signedEstimate score (cell U cuts)) z := hz
      simp [smallStep,smallPost,hh,hz',hz]
    · have hz' : ¬ (∑ e, |score e|)/(8*(J:ℝ)) ≤ candidateContrast hJ policy origin cutter cuts
        (positiveIndices score) t (signedEstimate score (cell U cuts)) z := hz
      simp [smallStep,smallPost,hh,hz',hz]
  rw [heq,← ENNReal.ofReal_toReal (measure_ne_top (volume.prod volume) Eᶜ)]
  apply ENNReal.ofReal_le_ofReal
  change (volume.prod volume).real Eᶜ ≤ _
  rw [measureReal_compl hE,probReal_univ]
  linarith

end EnvyFreeResearch.Full.UpperSnapshotRepetition
