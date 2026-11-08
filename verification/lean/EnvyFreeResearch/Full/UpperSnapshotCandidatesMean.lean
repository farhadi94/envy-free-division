import EnvyFreeResearch.Full.UpperSnapshotCandidatesSmall

/-! Elementary expectation-to-witness conversion for the small branch.
The actual circular-program mean and endpoint laws are separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
variable {X : Type*} [MeasurableSpace X]

/-- Ties are included in the estimated witness event. This scalar lemma
requires its actual mean; it does not assume a conditional success law. -/
theorem witness_chance_from_mean (P : Measure X) [IsProbabilityMeasure P]
    (score : X → ℝ) (hmeas : Measurable score) (hint : Integrable score P)
    (D agents : ℝ) (hD : 0 < D) (hagents : 0 < agents)
    (hbound : ∀ x, score x ≤ D) (hmean : D / (4 * agents) ≤ ∫ x, score x ∂P) :
    1 / (8 * agents) ≤ P.real {x | D / (8 * agents) ≤ score x} := by
  let S : Set X := {x | D / (8 * agents) ≤ score x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hmeas
  have ha : 0 ≤ D / (8 * agents) := by positivity
  have hpoint (x : X) : score x ≤ D / (8 * agents) + S.indicator (fun _ => D) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      linarith [hbound x]
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hi : Integrable (fun x => S.indicator (fun _ => D) x) P := (integrable_const D).indicator hS
  have hb := integral_mono hint ((integrable_const (D / (8 * agents))).add hi) hpoint
  change (∫ x, score x ∂P) ≤ ∫ x, D / (8 * agents) + S.indicator (fun _ => D) x ∂P at hb
  rw [integral_add (integrable_const _) hi, integral_const, integral_indicator_const D hS] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hb
  change (∫ x, score x ∂P) ≤ D / (8 * agents) + P.real S * D at hb
  have he : D / (4 * agents) = D / (8 * agents) + D * (1 / (8 * agents)) := by ring
  rw [he] at hmean
  change 1 / (8 * agents) ≤ P.real S
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotCandidates
