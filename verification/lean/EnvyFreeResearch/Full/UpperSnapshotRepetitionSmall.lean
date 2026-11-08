import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallChance
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallMeasurable

/-! Concrete history-adapted small-candidate amplification. The per-trial
chance is derived from the executed two-circle candidate, not supplied as
an abstract success certificate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable Chores
variable {n m J : ℕ}

theorem actual_small_failure_quarter
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (U : Set ℝ) (hpositive : 0 < (μ cutter).real U)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hlast : cuts (Fin.last (m+1))=1)
    (hmono : Monotone cuts) (score : Fin (m+1) → ℝ)
    (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hJ : 2≤J)
    (hfit : (J:ℝ)*t<1) (htlower : 1/(2*(J:ℝ))≤t)
    (hsum : ∑ e, score e=0) (hnull : ∀ e, volume (cell U cuts e)=0 → score e=0)
    (hD : 0<∑ e, |score e|) (origin : State n) (hs : smallValid μ U cuts origin) :
    law (volume.prod volume : Measure (Circle × Circle)) (16*J) {tape |
      (run (smallStep policy cutter cuts (positiveIndices score) t
        (interpolationCheck hJ cutter cuts score U t)) (drawList tape) origin).2=none} ≤
      ENNReal.ofReal ((1:ℝ)/4) := by
  apply run_failure_sixteen (volume.prod volume : Measure (Circle × Circle))
    (smallStep policy cutter cuts (positiveIndices score) t (interpolationCheck hJ cutter cuts score U t))
    (small_next_measurable hJ policy hmeas cutter cuts score U t)
    (small_reject_measurable hJ policy hmeas cutter cuts score U t)
    (smallValid μ U cuts) ?_ J (by omega) ?_ origin hs
  · intro state z hstate _
    exact small_valid_preserved μ policy hpolicy cutter U hpositive cuts hzero hmono score t ht hhalf hJ state hstate z
  · intro state hstate
    exact small_failure_bound μ policy hpolicy cutter U hpositive cuts hzero hlast hmono score t ht hhalf hJ
      hmeas hfit htlower hsum hnull hD state hstate

end EnvyFreeResearch.Full.UpperSnapshotRepetition
