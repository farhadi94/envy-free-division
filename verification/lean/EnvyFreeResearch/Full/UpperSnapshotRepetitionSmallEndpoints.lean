import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallMeasurable
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateTwoCircle
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallChance

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells UpperStageMeasurable Chores
variable {n m J : ℕ}

def smallEndpoints (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (s : State n) (z : Circle × Circle) : Fin (2+J) → ℝ :=
  Fin.append (firstRun policy s cutter cuts selected t z.1).1
    (secondRun (J:=J) policy s cutter cuts selected t z.1 z.2).1

theorem smallEndpoints_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (cutter : Fin n) (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (j : Fin (2+J)) :
    Measurable (fun p : State n × (Circle × Circle) => smallEndpoints policy cutter cuts selected t p.1 p.2 j) := by
  have hf := firstRun_measurable (fun p : State n × (Circle × Circle) => p.1) cutter
    (fun _ => cuts) (fun _ => selected) (fun _ => t) measurable_fst (fun _ => measurable_const)
    measurable_const measurable_const policy hmeas (fun p => p.2.1) (measurable_fst.comp measurable_snd)
  have hg := secondRun_measurable (X := State n × (Circle × Circle)) (J:=J) policy hmeas
    Prod.fst cutter (fun _ => cuts) (fun _ => selected) t (fun p => p.2.1) (fun p => p.2.2)
    measurable_fst (fun _ => measurable_const) measurable_const (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [smallEndpoints,Fin.append_left]
    exact (measurable_pi_apply i).comp (measurable_fst.comp hf)
  · intro i
    simp only [smallEndpoints,Fin.append_right]
    exact (measurable_pi_apply i).comp (measurable_fst.comp hg)

theorem smallEndpoints_sum (policy : Policy n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (s : State n) (z : Circle × Circle) (u : ℝ → ℝ≥0∞) :
    (∑ j, u (smallEndpoints (J:=J) policy cutter cuts selected t s z j)) =
      (∑ j, u ((firstRun policy s cutter cuts selected t z.1).1 j)) +
      ∑ j, u ((secondRun (J:=J) policy s cutter cuts selected t z.1 z.2).1 j) := by
  rw [Fin.sum_univ_add]
  simp only [smallEndpoints,Fin.append_left,Fin.append_right]

theorem smallEndpoints_conditional_charge {Row : Type*} [Fintype Row] [Nonempty Row]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (cutter : Row)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (U : Set ℝ) (horigin : domain origin.cells=U)
    (hpositive : 0 < (μ (active cutter)).real U)
    (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0) (hmono : Monotone cuts)
    (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0<t) (hhalf : t≤1/2)
    (s : State n) (hs : smallValid μ U cuts s) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ z : Circle × Circle, ∑ j, u (smallEndpoints (J:=J) policy (active cutter) cuts selected t s z j)
      ∂volume.prod volume) ≤
      (((J+2:ℕ):ℝ≥0∞)*ENNReal.ofReal (1/t)*Fintype.card Row)*
        ∫⁻ x,u x ∂UpperMixtureSampling.mixture μ active origin.cells := by
  have hmix : UpperMixtureSampling.mixture μ active s.cells = UpperMixtureSampling.mixture μ active origin.cells := by
    simp only [UpperMixtureSampling.mixture,hs.2.1,horigin]
  simp only [smallEndpoints_sum]
  simpa only [hmix] using UpperSnapshotEndpointAggregate.two_circle_charge μ active cutter policy hpolicy hmeas
    s hs.1 (by rw [hs.2.1]; exact hpositive) cuts hzero hmono hs.2.2 selected t ht hhalf u hu

end EnvyFreeResearch.Full.UpperSnapshotRepetition
