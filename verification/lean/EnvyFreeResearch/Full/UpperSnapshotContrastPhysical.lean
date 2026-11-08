import EnvyFreeResearch.Full.UpperSnapshotContrastMargin

/-! Raw physical margins use the actual reserve lower-mass check. Only
finite measures are needed here; no absolute continuity is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
variable {k : ℕ}

def normalizedValues (μ : Fin k → Measure ℝ) (reserve : Set ℝ) (allocation : Fin k → Set ℝ)
    (i j : Fin k) : ℝ := (μ i).real (allocation j) / (μ i).real reserve

def physicalGap (chores : Bool) (μ : Fin k → Measure ℝ) (allocation : Fin k → Set ℝ) (i j : Fin k) : ℝ :=
  signedGap chores (fun i j => (μ i).real (allocation j)) i j

theorem normalized_gap (chores : Bool) (μ : Fin k → Measure ℝ) (reserve : Set ℝ)
    (allocation : Fin k → Set ℝ) (i j : Fin k) :
    signedGap chores (normalizedValues μ reserve allocation) i j = physicalGap chores μ allocation i j / (μ i).real reserve := by
  cases chores <;> simp [signedGap, normalizedValues, physicalGap, sub_div]

theorem raw_gap (chores : Bool) (μ : Fin k → Measure ℝ) (reserve : Set ℝ)
    (allocation : Fin k → Set ℝ) (i j : Fin k) (hreserve : (μ i).real reserve ≠ 0) :
    physicalGap chores μ allocation i j = (μ i).real reserve * signedGap chores (normalizedValues μ reserve allocation) i j := by
  rw [normalized_gap]
  field_simp

/-- Convert the concrete maximizing normalized margin to an original-unit
margin against the actual residue. This covers cake and chores uniformly. -/
theorem exists_physical_margin (hk : 0 < k) (chores : Bool) (μ : Fin k → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (buffer reserve residue : Set ℝ) (allocation : Fin k → Set ℝ)
    (V e : Fin k → Fin k → ℝ) (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, normalizedValues μ reserve allocation i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores (normalizedValues μ reserve allocation) i j)
    (i h u v : Fin k) (Lambda theta : ℝ) (hLambda : 0 < Lambda) (htheta : 0 < theta)
    (hcontrast : Lambda / theta ≤ contrast V i h u v)
    (hbuffer : ∀ i, 0 < (μ i).real buffer)
    (hreserve : ∀ i, theta / 2 * (μ i).real buffer ≤ (μ i).real reserve)
    (hresidue : residue ⊆ buffer) :
    ∃ a b, a ≠ b ∧ 0 < physicalGap chores μ allocation a b ∧
      Lambda / 8 * (μ a).real residue ≤ physicalGap chores μ allocation a b ∧
      ∀ c d, signedGap chores (normalizedValues μ reserve allocation) c d ≤
        signedGap chores (normalizedValues μ reserve allocation) a b := by
  obtain ⟨a, b, hab, hlarge, hmax⟩ := exists_large_gap hk chores V (normalizedValues μ reserve allocation) e
    pi t hvalues herr i h u v Lambda theta hLambda htheta hcontrast
  have hmass : 0 < (μ a).real reserve :=
    (mul_pos (div_pos htheta (by norm_num)) (hbuffer a)).trans_le (hreserve a)
  have hgap : 0 < signedGap chores (normalizedValues μ reserve allocation) a b :=
    (div_pos hLambda (by positivity)).trans_le hlarge
  have hraw := raw_gap chores μ reserve allocation a b hmass.ne'
  refine ⟨a, b, hab, ?_, ?_, hmax⟩
  · rw [hraw]
    exact mul_pos hmass hgap
  · calc
      Lambda / 8 * (μ a).real residue ≤ Lambda / 8 * (μ a).real buffer :=
        mul_le_mul_of_nonneg_left (measureReal_mono hresidue) (by positivity)
      _ = (theta / 2 * (μ a).real buffer) * (Lambda / (4 * theta)) := by
        field_simp
        ring
      _ ≤ (μ a).real reserve * (Lambda / (4 * theta)) :=
        mul_le_mul_of_nonneg_right (hreserve a) (by positivity)
      _ ≤ (μ a).real reserve * signedGap chores (normalizedValues μ reserve allocation) a b :=
        mul_le_mul_of_nonneg_left hlarge hmass.le
      _ = physicalGap chores μ allocation a b := hraw.symm

end EnvyFreeResearch.Full.UpperSnapshotContrast
