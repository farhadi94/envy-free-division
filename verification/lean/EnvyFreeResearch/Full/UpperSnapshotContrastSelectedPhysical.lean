import EnvyFreeResearch.Full.UpperSnapshotContrastPhysical
import EnvyFreeResearch.Full.UpperSnapshotContrastSelection

/-! The Borel first maximizing pair realizes the physical margin certificate;
no existential choice is passed to a protocol. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
variable {k : ℕ}

theorem maximizingPair_physical (hk : 0 < k) (chores : Bool) (μ : Fin k → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (buffer reserve residue : Set ℝ) (allocation : Fin k → Set ℝ)
    (V e : Fin k → Fin k → ℝ) (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, normalizedValues μ reserve allocation i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores (normalizedValues μ reserve allocation) i j)
    (i h u v : Fin k) (Lambda theta : ℝ) (hLambda : 0 < Lambda) (htheta : 0 < theta)
    (hcontrast : Lambda / theta ≤ contrast V i h u v)
    (hbuffer : ∀ i, 0 < (μ i).real buffer)
    (hreserve : ∀ i, theta / 2 * (μ i).real buffer ≤ (μ i).real reserve)
    (hresidue : residue ⊆ buffer) :
    let p := maximizingPair hk chores (normalizedValues μ reserve allocation)
    p.1 ≠ p.2 ∧ 0 < physicalGap chores μ allocation p.1 p.2 ∧
      Lambda / 8 * (μ p.1).real residue ≤ physicalGap chores μ allocation p.1 p.2 := by
  let p := maximizingPair hk chores (normalizedValues μ reserve allocation)
  have hp := maximizingPair_large hk chores V (normalizedValues μ reserve allocation) e pi t
    hvalues herr i h u v Lambda theta hLambda htheta hcontrast
  have hmass : 0 < (μ p.1).real reserve :=
    (mul_pos (div_pos htheta (by norm_num)) (hbuffer p.1)).trans_le (hreserve p.1)
  have hgap : 0 < signedGap chores (normalizedValues μ reserve allocation) p.1 p.2 :=
    (div_pos hLambda (by positivity)).trans_le hp.2
  have hraw := raw_gap chores μ reserve allocation p.1 p.2 hmass.ne'
  refine ⟨hp.1, ?_, ?_⟩
  · rw [hraw]
    exact mul_pos hmass hgap
  · calc
      Lambda / 8 * (μ p.1).real residue ≤ Lambda / 8 * (μ p.1).real buffer :=
        mul_le_mul_of_nonneg_left (measureReal_mono hresidue) (by positivity)
      _ = (theta / 2 * (μ p.1).real buffer) * (Lambda / (4 * theta)) := by
        field_simp
        ring
      _ ≤ (μ p.1).real reserve * (Lambda / (4 * theta)) :=
        mul_le_mul_of_nonneg_right (hreserve p.1) (by positivity)
      _ ≤ (μ p.1).real reserve * signedGap chores (normalizedValues μ reserve allocation) p.1 p.2 :=
        mul_le_mul_of_nonneg_left hp.2 hmass.le
      _ = physicalGap chores μ allocation p.1 p.2 := hraw.symm

end EnvyFreeResearch.Full.UpperSnapshotContrast
