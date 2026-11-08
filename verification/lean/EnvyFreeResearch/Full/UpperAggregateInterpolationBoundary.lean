import EnvyFreeResearch.Full.UpperAggregateInterpolationUnions

/-! Original immutable-grid boundaries have exactly zero cumulative error. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperGridInterpolation UpperGridSensitivity UpperRecordedDomain UpperLogicalCells

theorem linearEstimate_at_boundary {n : ℕ} (F L : ℝ → ℝ) (cuts : Fin (n + 2) → ℝ)
    (hmono : Monotone cuts)
    (hflat : ∀ e : Fin (n + 1), L (cuts e.succ) = L (cuts e.castSucc) →
      F (cuts e.succ) = F (cuts e.castSucc)) (p : Fin (n + 2)) :
    linearEstimate F L cuts (cuts p) = F (cuts p) := by
  refine Fin.lastCases ?_ (fun e => ?_) p
  · let e : Fin (n + 1) := Fin.last n
    have heq : e.succ = Fin.last (n + 1) := rfl
    rw [← heq]
    rw [linearEstimate_local F L cuts hmono hflat _ e
      (hmono (by simp [Fin.le_def])) le_rfl]
    by_cases hzero : L (cuts e.succ) = L (cuts e.castSucc)
    · simp [hzero, hflat e hzero]
    · rw [div_self (sub_ne_zero.mpr hzero)]
      ring
  · rw [linearEstimate_local F L cuts hmono hflat _ e le_rfl
      (hmono (by simp [Fin.le_def]))]
    simp

theorem linearError_at_boundary {Row : Type*} [Fintype Row] [Nonempty Row] {n : ℕ}
    (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (hflat : FlatCompatible F L)
    (cuts : Fin (n + 2) → ℝ) (hmono : Monotone cuts) (p : Fin (n + 2)) (i j : Row) :
    linearError F L cuts (cuts p) i j = 0 := by
  have hflat' (r : Row) (e : Fin (n + 1))
      (he : L (cuts e.succ) = L (cuts e.castSucc)) : F r (cuts e.succ) = F r (cuts e.castSucc) :=
    (hflat r _ _ (hmono (by simp [Fin.le_def])) he.symm).symm
  rw [linearError, linearEstimate_at_boundary (F i) L cuts hmono (hflat' i),
    linearEstimate_at_boundary (F j) L cuts hmono (hflat' j), sub_self, abs_zero]

theorem physicalError_at_boundary {Row : Type*} [Fintype Row] [Nonempty Row] {n : ℕ}
    (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (cs : List Component) (cuts : Fin (n + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0) (p : Fin (n + 2)) (i j : Row) :
    physicalError μ normalizer cs cuts (cuts p) i j = 0 := by
  have h := linearError_at_boundary (normalizedCumulative μ normalizer cs)
    (domainCumulative volume cs) (normalizedCumulative_flat μ normalizer cs) cuts hmono p i j
  simpa only [linearError, physicalError,
    linearEstimate_sub_eq_envelope μ normalizer cs cuts hmono hzero] using h

/-- No charge is assigned to any original grid boundary, even when logical
cells are empty, duplicate-boundary cells, or zero-volume physical fragments. -/
theorem physicalMaximum_at_boundary {Row : Type*} [Fintype Row] [Nonempty Row] {n : ℕ}
    (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (cs : List Component) (cuts : Fin (n + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0) (p : Fin (n + 2)) :
    physicalMaximum μ normalizer cs cuts (cuts p) = 0 := by
  simp [physicalMaximum, physicalError_at_boundary μ normalizer cs cuts hmono hzero p]

end EnvyFreeResearch.Full.UpperAggregateInterpolation
