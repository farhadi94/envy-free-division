import EnvyFreeResearch.Full.UpperSnapshotSmallSecondMeasurable

/-! A total Borel implementation of the immutable interpolation score.
It is defined even on malformed component lists and equals physical signed
mass whenever the recorded components are disjoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperDomainDifference
variable {Cell : Type*} [Fintype Cell] {X : Type*} [MeasurableSpace X]

def interpolatedTotal (score : Cell → ℝ) (cells : Cell → Set ℝ) (cs : List Component) : ℝ :=
  ∑ e, score e * sumValues (mass (cond volume (cells e))) cs

theorem interpolatedTotal_measurable (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (cs : X → List Component) (hcs : Measurable cs) :
    Measurable (fun x => interpolatedTotal score cells (cs x)) := by
  apply Finset.measurable_sum
  intro e _
  letI : NullSingletonClass (cond volume (cells e)) := by
    constructor
    intro x
    rw [ProbabilityTheory.cond_apply' (measurableSet_singleton x)]
    have hz : volume (cells e ∩ {x}) = 0 :=
      measure_mono_null inter_subset_right (measure_singleton x)
    rw [hz, mul_zero]
  exact measurable_const.mul (sumValues_mass_measurable (cond volume (cells e)) cs hcs)

theorem interpolatedTotal_correct (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (cs : List Component) (hcs : DisjointComponents cs) :
    interpolatedTotal score cells cs = signedEstimate score cells (domain cs) := by
  rw [signedEstimate_apply score cells _ (domain_measurable cs)]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact (domain_mass_sum (cond volume (cells e)) cs hcs).symm

end EnvyFreeResearch.Full.UpperSnapshotSmall
