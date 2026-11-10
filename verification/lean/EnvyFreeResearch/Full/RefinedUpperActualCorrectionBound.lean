import EnvyFreeResearch.Full.RefinedUpperStabilityActualControl
import EnvyFreeResearch.Full.RefinedUpperBadMass
import EnvyFreeResearch.Full.RefinedUpperCorrectionBatchProbability

/-! Conditional failure bound for the actual sampled correction stage.
The pointwise stability and endpoint-mass hypotheses are discharged from
the original-mixture bad mass, including inherited boundaries. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperActualCorrectionBound
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage RefinedUpperPreparation
  RefinedUpperStability RefinedUpperCorrectionSetup UpperStageMeasurable UpperPreparedEnvelopeMean
variable {n k : ℕ} [Nonempty (Fin k)]

def finalJobs (k : ℕ) : List (Fin k × Fin k) := Finset.univ.toList

theorem correction_probability
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 4*(UpperRepairJobs.jobCount k*L) ≤ q+1)
    (t : Fin k → ℝ) (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hsize : 16*(k : ℝ) ≤ lam) (hmargin : (k : ℝ)*lam*eta < 1/16)
    (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1)))
    (hc : Checks μ active
      (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L)
      (UpperGridMerge.cuts policy active origin q m draw) t eta selected N)
    (δ : ℝ≥0∞)
    (hbadmass : UpperMixtureSampling.mixture μ active origin.cells
      (physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L) (finalJobs k)
        (UpperGridMerge.prepare policy active origin q m draw).1
        (UpperGridMerge.prepare policy active origin q m draw).2.1) ≤ δ)
    (a b B : ℝ≥0∞) (hbadbound : ENNReal.ofReal (32*(k : ℝ)/7)*δ ≤ a)
    (henvelope : ENNReal.ofReal (8*eta*N/lam) ≤ b) (hfixed : a+B*b ≤ B) (r : ℕ) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let reserve := dataRetained active origin data L
    UpperAdaptiveProduct.tapeLaw
      (UpperAdaptiveProduct.tapeLaw (volume : Measure UpperCircular.Circle) r) k
      {tape | (RefinedUpperBatchLoop.run policy
        (tasks active reserve (UpperGridData.cuts data) t eta lam)
        (startState active reserve (UpperGridData.cuts data) t eta) tape).2.stopped = true} ≤
      (k : ℝ≥0∞)*(B+b^r) := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let reserve := dataRetained active origin data L
  let bad := physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L)
    (finalJobs k) data.1 data.2.1
  let augmented := RefinedUpperEndpointExceptions.augment bad (domain reserve.cells) (UpperGridData.cuts data)
  have hmeas : MeasurableSet augmented := RefinedUpperEndpointExceptions.augment_measurable
    bad (domain reserve.cells) (UpperGridData.cuts data)
    (physicalBad_measurable μ policy active origin q _ _ _ _) (domain_measurable _)
  have hsub : domain reserve.cells ⊆ domain origin.cells := by
    rw [show domain reserve.cells = ⋃ p, if p ∉ (dataResult active origin data L).2 then
      UpperRecordedQuantiles.logicalCells policy active origin q p else ∅ from
      retainedState_domain μ policy hp active origin hgood hpositive q m draw _]
    apply iUnion_subset
    intro p
    split_ifs
    · exact empty_subset _
    · exact UpperLogicalCells.cell_subset _ _ _
  apply RefinedUpperCorrectionBatchProbability.stopped_probability μ policy hp hm active hinj
    reserve (UpperGridData.cuts data) t eta lam N heta hlam hN hsize hmargin selected hc augmented hmeas
  · intro x hx i j
    exact actual_point_control μ policy hp active origin hgood hpositive q m L draw
      (by omega) (finalJobs k) x hx i j (by simp [finalJobs])
  · exact hpositive
  · exact dataRetained_half μ policy hp active origin hgood hpositive q m L draw hbudget
  · exact RefinedUpperBadMass.retained_augmented_mass μ active origin.cells (domain reserve.cells)
      bad (UpperGridData.cuts data) (domain_measurable _) hsub δ hbadmass
  · exact hbadbound
  · exact henvelope
  · exact hfixed

end EnvyFreeResearch.Full.RefinedUpperActualCorrectionBound
