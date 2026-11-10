import EnvyFreeResearch.Full.UpperAggregateInterpolationPhysical

/-!
# Interpolation error at good endpoints, including inherited boundaries

A good endpoint controls both parts of its original grid cell. Convexity
bounds its interpolation error by 2A, rather than adding the two bounds.
The physical finite-union telescope charges every retained boundary. Thus
at most 2k boundaries cost 4k A, even after earlier accepted corrections.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.RefinedUpperBoundaryError

open UpperGridInterpolation UpperAggregateInterpolation UpperRecordedDomain

theorem convex_error_le (a b theta B : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (ha : |a| ≤ B) (hb : |b| ≤ B) :
    |(1 - theta) * a - theta * b| ≤ B := by
  calc
    _ ≤ |(1 - theta) * a| + |theta * b| := abs_sub _ _
    _ = (1 - theta) * |a| + theta * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1 - theta) * B + theta * B :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hb ht0)
    _ = B := by ring

/-- Prefix and suffix bounds hold in the original cell, not the current
fragment. Their convex combination controls cumulative interpolation. -/
theorem linearError_le {Row : Type*} [Fintype Row] [Nonempty Row] {m : ℕ}
    (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (cuts : Fin (m + 1) → ℝ)
    (hcuts : Monotone cuts) (hL : Monotone L)
    (hflat : ∀ r (e : Fin m), L (cuts e.succ) = L (cuts e.castSucc) →
      F r (cuts e.succ) = F r (cuts e.castSucc))
    (z : ℝ) (e : Fin m) (hl : cuts e.castSucc ≤ z) (hr : z ≤ cuts e.succ)
    (i j : Row) (A : ℝ)
    (hp : |(F i z - F i (cuts e.castSucc)) -
      (F j z - F j (cuts e.castSucc))| ≤ 2 * A)
    (hs : |(F i (cuts e.succ) - F i z) -
      (F j (cuts e.succ) - F j z)| ≤ 2 * A) :
    linearError F L cuts z i j ≤ 2 * A := by
  let theta := (L z - L (cuts e.castSucc)) / (L (cuts e.succ) - L (cuts e.castSucc))
  have ht0 : 0 ≤ theta := div_nonneg (sub_nonneg.mpr (hL hl))
    (sub_nonneg.mpr (hL (hl.trans hr)))
  have ht1 : theta ≤ 1 := div_le_one_of_le₀ (sub_le_sub_right (hL hr) _)
    (sub_nonneg.mpr (hL (hl.trans hr)))
  unfold linearError
  rw [linearEstimate_local (F i) L cuts hcuts (hflat i) z e hl hr,
    linearEstimate_local (F j) L cuts hcuts (hflat j) z e hl hr]
  convert convex_error_le
    ((F i z - F i (cuts e.castSucc)) - (F j z - F j (cuts e.castSucc)))
    ((F i (cuts e.succ) - F i z) - (F j (cuts e.succ) - F j z))
    theta (2 * A) ht0 ht1 hp hs using 1 <;> dsimp [theta] <;> congr 1 <;> ring

/-- This statement uses actual finite atomless measures and actual buffer
volume. No density bound or absolute continuity is needed. -/
theorem physicalError_le {Row : Type*} [Fintype Row] [Nonempty Row] {m : ℕ}
    (μ : Row → Measure ℝ) [∀ r, IsFiniteMeasure (μ r)] [∀ r, NullSingletonClass (μ r)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (m + 2) → ℝ)
    (hcuts : Monotone cuts) (hzero : cuts 0 = 0)
    (z : ℝ) (e : Fin (m + 1)) (hl : cuts e.castSucc ≤ z) (hr : z ≤ cuts e.succ)
    (i j : Row) (A : ℝ)
    (hp : |(normalizedCumulative μ normalizer buffer i z -
        normalizedCumulative μ normalizer buffer i (cuts e.castSucc)) -
      (normalizedCumulative μ normalizer buffer j z -
        normalizedCumulative μ normalizer buffer j (cuts e.castSucc))| ≤ 2 * A)
    (hs : |(normalizedCumulative μ normalizer buffer i (cuts e.succ) -
        normalizedCumulative μ normalizer buffer i z) -
      (normalizedCumulative μ normalizer buffer j (cuts e.succ) -
        normalizedCumulative μ normalizer buffer j z)| ≤ 2 * A) :
    physicalError μ normalizer buffer cuts z i j ≤ 2 * A := by
  have hf (r : Row) (e : Fin (m + 1))
      (he : domainCumulative volume buffer (cuts e.succ) =
        domainCumulative volume buffer (cuts e.castSucc)) :=
    (normalizedCumulative_flat μ normalizer buffer r _ _
      (hcuts (by simp [Fin.le_def])) he.symm).symm
  have h := linearError_le (normalizedCumulative μ normalizer buffer)
    (domainCumulative volume buffer) cuts hcuts
    (domainCumulative_monotone volume buffer (domain_volume_finite buffer))
    hf z e hl hr i j A hp hs
  simpa only [linearError, physicalError,
    linearEstimate_sub_eq_envelope μ normalizer buffer cuts hcuts hzero] using h

/-- All inherited endpoints are included in Generated. Counting only the
latest two endpoints would not justify this conclusion. -/
theorem retained_boundary_bound {Row Generated : Type*}
    [Fintype Row] [Nonempty Row] [Fintype Generated] {m k : ℕ}
    (μ : Row → Measure ℝ) [∀ r, IsFiniteMeasure (μ r)] [∀ r, NullSingletonClass (μ r)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (m + 2) → ℝ)
    (hcuts : Monotone cuts) (hzero : cuts 0 = 0) (points : Generated → ℝ)
    (pieces : List Component)
    (hendpoints : ∀ c ∈ pieces,
      ((∃ p, cuts p = c.left) ∨ ∃ g, points g = c.left) ∧
      ((∃ p, cuts p = c.right) ∨ ∃ g, points g = c.right))
    (i j : Row) (A : ℝ) (hA : 0 ≤ A) (hcount : Fintype.card Generated ≤ 2 * k)
    (hgood : ∀ g, physicalError μ normalizer buffer cuts (points g) i j ≤ 2 * A) :
    |discrepancy μ normalizer buffer cuts i j (domain pieces)| ≤ 4 * k * A := by
  calc
    _ ≤ ∑ g, physicalError μ normalizer buffer cuts (points g) i j :=
      physical_recorded_union_error_le μ normalizer buffer cuts hcuts hzero points pieces hendpoints i j
    _ ≤ ∑ _ : Generated, 2 * A := Finset.sum_le_sum (fun g _ => hgood g)
    _ = (Fintype.card Generated : ℝ) * (2 * A) := by simp
    _ ≤ (2 * (k : ℝ)) * (2 * A) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcount) (by positivity)
    _ = 4 * k * A := by ring

end EnvyFreeResearch.Full.RefinedUpperBoundaryError
