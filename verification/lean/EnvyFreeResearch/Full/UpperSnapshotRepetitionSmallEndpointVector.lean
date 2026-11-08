import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpoints
import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpointVector

/-! The fixed finite vector contains every reached two-circle endpoint group,
including rejected candidates. Later unused slots contain the known grid zero. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable Chores
variable {n m J : ℕ}

def smallEndpointVector (hJ : 2 ≤ J) (policy : Policy n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ)
    (origin : State n) (tape : Tape (Circle × Circle) (16*J)) : Fin ((16*J)*(2+J)) → ℝ :=
  endpointVector
    (fun s z => (smallStep policy cutter cuts (positiveIndices score) t (interpolationCheck hJ cutter cuts score U t) s z).1)
    (fun s z => (smallStep policy cutter cuts (positiveIndices score) t (interpolationCheck hJ cutter cuts score U t) s z).2.isNone)
    (smallEndpoints policy cutter cuts (positiveIndices score) t) (16*J) origin tape

theorem smallEndpointVector_measurable (hJ : 2 ≤ J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ)
    (origin : State n) (j : Fin ((16*J)*(2+J))) :
    Measurable (fun tape => smallEndpointVector hJ policy cutter cuts score U t origin tape j) :=
  (endpointVector_measurable _ _ _
    (small_next_measurable hJ policy hmeas cutter cuts score U t)
    (small_reject_measurable hJ policy hmeas cutter cuts score U t)
    (smallEndpoints_measurable policy hmeas cutter cuts (positiveIndices score) t) (16*J) j).comp
    (measurable_const.prodMk measurable_id)

theorem actual_small_endpoints_expectation {Row : Type*} [Fintype Row] [Nonempty Row]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (cutter : Row)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (U : Set ℝ) (hpositive : 0 < (μ (active cutter)).real U)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (score : Fin (m+1) → ℝ) (t : ℝ) (ht : 0<t) (hhalf : t≤1/2) (hJ : 2≤J)
    (origin : State n) (hs : smallValid μ U cuts origin) (u : ℝ → ℝ≥0∞) (hu : Measurable u) (hu0 : u 0=0) :
    (∫⁻ tape, ∑ j, u (smallEndpointVector hJ policy (active cutter) cuts score U t origin tape j)
      ∂law (volume.prod volume : Measure (Circle × Circle)) (16*J)) ≤
      ((16*J:ℕ):ℝ≥0∞)*
        ((((J+2:ℕ):ℝ≥0∞)*ENNReal.ofReal (1/t)*Fintype.card Row)*
          ∫⁻ x,u x ∂UpperMixtureSampling.mixture μ active origin.cells) := by
  simp only [smallEndpointVector,endpointVector_charge _ _ _ u hu0]
  apply endpointCharge_expectation (volume.prod volume : Measure (Circle × Circle)) _ _ _ u
    (small_next_measurable hJ policy hmeas (active cutter) cuts score U t)
    (small_reject_measurable hJ policy hmeas (active cutter) cuts score U t)
    (smallEndpoints_measurable policy hmeas (active cutter) cuts (positiveIndices score) t) hu
    (smallValid μ U cuts) ?_ _ ?_ (16*J) origin hs
  · intro state z hstate _
    exact small_valid_preserved μ policy hpolicy (active cutter) U hpositive cuts hzero hmono score t ht hhalf hJ state hstate z
  · intro state hstate
    exact smallEndpoints_conditional_charge μ active cutter policy hpolicy hmeas origin U hs.2.1 hpositive
      cuts hzero hmono (positiveIndices score) t ht hhalf state hstate u hu

end EnvyFreeResearch.Full.UpperSnapshotRepetition
