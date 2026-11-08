import EnvyFreeResearch.Full.UpperAggregateInterpolationRecorded
import EnvyFreeResearch.Full.UpperAggregateInterpolationBoundary

/-!
# Telescoping for the actual immutable-grid physical envelope

The true normalized row difference and the envelope are encoded as a finite
real linear combination of their actual measures. The generic signed-union
calculation therefore applies to every literal recorded component union.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperLogicalCells UpperGridInterpolation UpperGridSensitivity

variable {Row : Type*} [Fintype Row] [Nonempty Row] {n : ℕ}

def discrepancy (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (buffer : List Component)
    (cuts : Fin (n + 2) → ℝ) (i j : Row) (E : Set ℝ) : ℝ :=
  (μ i).real (domain buffer ∩ E) / normalizer i -
    (μ j).real (domain buffer ∩ E) / normalizer j -
    UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
      (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j E

def discrepancyMeasures (μ : Row → Measure ℝ) (buffer : List Component)
    (cuts : Fin (n + 2) → ℝ) (i j : Row) : Bool ⊕ Fin (n + 1) → Measure ℝ
  | .inl false => (μ i).restrict (domain buffer)
  | .inl true => (μ j).restrict (domain buffer)
  | .inr e => UpperEnvelope.uniformCells (cell (domain buffer) cuts) e

def discrepancyCoefficients (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (buffer : List Component)
    (cuts : Fin (n + 2) → ℝ) (i j : Row) : Bool ⊕ Fin (n + 1) → ℝ
  | .inl false => 1 / normalizer i
  | .inl true => -(1 / normalizer j)
  | .inr e => -(physicalRows μ normalizer buffer cuts i e - physicalRows μ normalizer buffer cuts j e)

instance discrepancyMeasures_finite (μ : Row → Measure ℝ) [∀ r, IsFiniteMeasure (μ r)]
    (buffer : List Component) (cuts : Fin (n + 2) → ℝ) (i j : Row) (t : Bool ⊕ Fin (n + 1)) :
    IsFiniteMeasure (discrepancyMeasures μ buffer cuts i j t) := by
  rcases t with b | e
  · cases b <;> dsimp [discrepancyMeasures] <;> infer_instance
  · dsimp [discrepancyMeasures]; infer_instance

instance discrepancyMeasures_atomless (μ : Row → Measure ℝ) [∀ r, NullSingletonClass (μ r)]
    (buffer : List Component) (cuts : Fin (n + 2) → ℝ) (i j : Row) (t : Bool ⊕ Fin (n + 1)) :
    NullSingletonClass (discrepancyMeasures μ buffer cuts i j t) := by
  rcases t with b | e
  · cases b <;> dsimp [discrepancyMeasures] <;> infer_instance
  · refine ⟨fun x => ?_⟩
    change (ProbabilityTheory.cond volume (cell (domain buffer) cuts e)) {x} = 0
    rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
    have hz : volume ({x} ∩ cell (domain buffer) cuts e) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton x)
    simp [hz]

theorem discrepancy_eq_signedValue (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (n + 2) → ℝ) (i j : Row)
    (E : Set ℝ) (hE : MeasurableSet E) :
    discrepancy μ normalizer buffer cuts i j E =
      signedValue (discrepancyCoefficients μ normalizer buffer cuts i j)
        (discrepancyMeasures μ buffer cuts i j) E := by
  have hr (r : Row) : ((μ r).restrict (domain buffer)).real E = (μ r).real (domain buffer ∩ E) := by
    rw [measureReal_def, Measure.restrict_apply hE, inter_comm]
    rfl
  simp only [signedValue, Fintype.sum_sum_type, Fintype.sum_bool,
    discrepancyCoefficients, discrepancyMeasures, hr, neg_mul, Finset.sum_neg_distrib,
    discrepancy, UpperEnvelope.estimate, div_eq_mul_inv, one_mul]
  ring

theorem discrepancy_prefix_abs (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (n + 2) → ℝ) (i j : Row) (z : ℝ) :
    |discrepancy μ normalizer buffer cuts i j (Iic z)| =
      physicalError μ normalizer buffer cuts z i j := rfl

/-- No interval-selection or telescoping bound is a premise: the theorem
constructs the distinct boundary grid and atomizes the literal component
union, and original immutable-grid boundaries vanish by exact interpolation. -/
theorem physical_recorded_union_error_le {Generated : Type*} [Fintype Generated]
    (μ : Row → Measure ℝ) [∀ r, IsFiniteMeasure (μ r)] [∀ r, NullSingletonClass (μ r)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (n + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0) (points : Generated → ℝ)
    (pieces : List Component)
    (hendpoints : ∀ c ∈ pieces,
      ((∃ p, cuts p = c.left) ∨ ∃ j, points j = c.left) ∧
      ((∃ p, cuts p = c.right) ∨ ∃ j, points j = c.right)) (i j : Row) :
    |discrepancy μ normalizer buffer cuts i j (domain pieces)| ≤
      ∑ g, physicalError μ normalizer buffer cuts (points g) i j := by
  let coeff := discrepancyCoefficients μ normalizer buffer cuts i j
  let laws := discrepancyMeasures μ buffer cuts i j
  have hprefix (z : ℝ) : |signedValue coeff laws (Iic z)| =
      physicalError μ normalizer buffer cuts z i j := by
    rw [← discrepancy_eq_signedValue μ normalizer buffer cuts i j _ measurableSet_Iic]
    rfl
  rw [discrepancy_eq_signedValue μ normalizer buffer cuts i j _ (domain_measurable pieces)]
  have hbound := arbitrary_recorded_union_error_le coeff laws pieces points ?_
  · simpa only [hprefix] using hbound
  · intro c hc
    have hat (x : ℝ) (hx : (∃ p, cuts p = x) ∨ ∃ j, points j = x) :
        signedValue coeff laws (Iic x) = 0 ∨ ∃ j, points j = x := by
      rcases hx with ⟨p, rfl⟩ | hx
      · left
        apply abs_eq_zero.mp
        rw [hprefix, physicalError_at_boundary μ normalizer buffer cuts hmono hzero p]
      · exact Or.inr hx
    exact ⟨hat c.left (hendpoints c hc).1, hat c.right (hendpoints c hc).2⟩

end EnvyFreeResearch.Full.UpperAggregateInterpolation
