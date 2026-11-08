import EnvyFreeResearch.Full.UpperLogicalCellNull

/-! Exact cumulative coordinates for interpolation inside logical cells. -/

noncomputable section

open MeasureTheory Set
open scoped Classical ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPrefix

open UpperRecordedDomain UpperLogicalCells

theorem cell_prefix_mass {m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (buffer : Set ℝ) (hbuffer : MeasurableSet buffer) (hfinite : μ buffer ≠ ∞)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) (i : Fin (m + 1)) (z : ℝ) :
    μ.real (cell buffer cuts i ∩ Iic z) =
      μ.real (buffer ∩ Iic (min (cuts i.succ) z)) -
      μ.real (buffer ∩ Iic (min (cuts i.castSucc) z)) := by
  let ν := μ.restrict (buffer ∩ Iic z)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (measure_ne_top_of_subset inter_subset_left hfinite)
  have h := cell_mass_prefix ν buffer hbuffer cuts hmono i
  simp only [ν, measureReal_restrict_apply' (hbuffer.inter measurableSet_Iic)] at h
  have hleft : cell buffer cuts i ∩ (buffer ∩ Iic z) = cell buffer cuts i ∩ Iic z := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, cell_subset buffer cuts i hx.1, hx.2⟩
  have hright (r : ℝ) : (buffer ∩ Iic r) ∩ (buffer ∩ Iic z) = buffer ∩ Iic (min r z) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, le_min_iff]
    tauto
  simpa only [hleft, hright] using h

/-- The cumulative-volume formula includes the first cell's literal endpoint
and arbitrary old physical gaps inside the logical cell. -/
theorem cell_volume_prefix {m : ℕ} (cells : List Component)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) (i : Fin (m + 1)) (z : ℝ) :
    volume.real (cell (domain cells) cuts i ∩ Iic z) =
      volume.real (domain cells ∩ Iic (min (cuts i.succ) z)) -
      volume.real (domain cells ∩ Iic (min (cuts i.castSucc) z)) :=
  cell_prefix_mass volume (domain cells) (domain_measurable cells)
    (measure_ne_top_of_subset (domain_subset_unit cells)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) cuts hmono i z

end EnvyFreeResearch.Full.UpperLogicalPrefix
