import EnvyFreeResearch.Full.UpperSnapshotSmallSecondExecution
import EnvyFreeResearch.Full.UpperSnapshotSmallSigned
import EnvyFreeResearch.Full.UpperDomainDifferenceDynamic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ} {X : Type*} [MeasurableSpace X]

/-- The second circle sees the full realized first-stage query history. -/
theorem secondPiece_measurable (hJ : 0 < J) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (origin : X → State n) (cutter : Fin n) (cuts : X → Fin (m + 2) → ℝ)
    (selected : X → Finset (Fin (m + 1))) (t : ℝ) (first second : X → Circle)
    (horigin : Measurable origin) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hselected : Measurable selected) (hfirst : Measurable first) (hsecond : Measurable second) (j : Fin J) :
    Measurable (fun x => secondPiece hJ policy (origin x) cutter (cuts x) (selected x) t (first x) (second x) j) := by
  exact partState_measurable hJ policy hmeas _ cutter (fun _ => remainderTargets J t) second
    (firstRemainder_measurable origin cutter cuts selected (fun _ => t) horigin hcuts hselected
      measurable_const policy hmeas first hfirst) (fun _ => measurable_const) hsecond j

variable {Cell : Type*} [Fintype Cell]

theorem signedEstimate_domain_measurable (score : Cell → ℝ) (cells : Cell → Set ℝ)
    (cs : X → List Component) (hcs : Measurable cs) (hdis : ∀ x, DisjointComponents (cs x)) :
    Measurable (fun x => signedEstimate score cells (domain (cs x))) := by
  have heq : (fun x => signedEstimate score cells (domain (cs x))) =
      fun x => ∑ e, score e * (cond volume (cells e)).real (domain (cs x)) := by
    funext x
    exact signedEstimate_apply score cells _ (domain_measurable _)
  rw [heq]
  apply Finset.measurable_sum
  intro e _
  letI : NullSingletonClass (cond volume (cells e)) := by
    constructor
    intro x
    rw [ProbabilityTheory.cond_apply' (measurableSet_singleton x)]
    have hz : volume (cells e ∩ {x}) = 0 :=
      measure_mono_null inter_subset_right (measure_singleton x)
    rw [hz, mul_zero]
  exact measurable_const.mul (domain_mass_measurable (cond volume (cells e)) cs hcs hdis)

end EnvyFreeResearch.Full.UpperSnapshotSmall
