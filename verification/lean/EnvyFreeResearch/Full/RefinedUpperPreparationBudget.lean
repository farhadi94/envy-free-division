import EnvyFreeResearch.Full.RefinedUpperPreparationWeights
import EnvyFreeResearch.Full.UpperLogicalIsolationBudget

/-! Actual new threshold packages preserve the quantitative near-envy budget
for both cake and chores. Bounds use retained-buffer normalizers. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperLogicalIsolation UpperSeedMatrix Chores
open scoped Classical unitInterval
variable {n k : ℕ} [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem dataMatrix_increment (hk : 2 ≤ k) (old : Fin k → State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 4*(jobCount k*L) ≤ q+1)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (i c : Fin k) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let V := dataMatrix hk active origin old data L pi threshold
    let W := oldMatrix active old (dataRetained active origin data L)
    0 ≤ V i c-W i c ∧ V i c-W i c ≤ k.choose 2*L*(2/(q+1 : ℝ)) :=
  matrix_increment_bound hk _
    (dataWeights_nonneg μ policy hpolicy active origin hgood hpositive q m L draw) _ (by positivity)
    (dataWeights_small μ policy hpolicy active origin hgood hpositive q m L draw hbudget) _ pi threshold i c

theorem dataMatrix_cake_near (hk : 2 ≤ k) (old : Fin k → State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 4*(jobCount k*L) ≤ q+1)
    (eps : ℝ)
    (hnear : ∀ i j,
      oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i j-
      oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i i ≤ eps)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (i : Fin k) :
    let V := dataMatrix hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold
    UpperIdealPayments.rowMaximum V i-V i i ≤ eps+k.choose 2*L*(2/(q+1 : ℝ)) :=
  matrix_cake_near hk _
    (dataWeights_nonneg μ policy hpolicy active origin hgood hpositive q m L draw) _ (by positivity)
    (dataWeights_small μ policy hpolicy active origin hgood hpositive q m L draw hbudget) _ eps hnear pi threshold i

theorem dataMatrix_chore_near (hk : 2 ≤ k) (old : Fin k → State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 4*(jobCount k*L) ≤ q+1)
    (eps : ℝ)
    (hnear : ∀ i j,
      oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i i-
      oldMatrix active old (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L) i j ≤ eps)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (i : Fin k) :
    let V := dataMatrix hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold
    UpperIdealPayments.rowMaximum (fun r c => -V r c) i+V i i ≤ eps+k.choose 2*L*(2/(q+1 : ℝ)) :=
  matrix_chore_near hk _
    (dataWeights_nonneg μ policy hpolicy active origin hgood hpositive q m L draw) _ (by positivity)
    (dataWeights_small μ policy hpolicy active origin hgood hpositive q m L draw hbudget) _ eps hnear pi threshold i

end EnvyFreeResearch.Full.RefinedUpperPreparation
