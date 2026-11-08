import EnvyFreeResearch.Full.UpperLogicalCells
import EnvyFreeResearch.Full.UpperMixtureSampling

/-!
# Quantile gaps bound every logical grid cell

Two consecutive common-grid coordinates contain no other grid coordinate
strictly between them. A normalized monotone cumulative function with every
interior `s`-quantile in that grid therefore changes by at most `1/s` on
each logical cell, including repeated grid coordinates and plateau roots.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperQuantileBounds

open UpperLogicalCells UpperUnionSampling

theorem no_grid_point_between {m : ℕ} (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts)
    (i : Fin (m + 1)) (j : Fin (m + 2)) :
    ¬ (cuts i.castSucc < cuts j ∧ cuts j < cuts i.succ) := by
  rintro ⟨hl, hr⟩
  by_cases hj : j ≤ i.castSucc
  · exact (not_lt_of_ge (hmono hj)) hl
  · have hj' : i.succ ≤ j := by
      change i.val + 1 ≤ j.val
      have hh : ¬ j.val ≤ i.val := hj
      omega
    exact (not_lt_of_ge (hmono hj')) hr

/-- A gap larger than one quantile step contains an interior quantile level.
The index is constructed from the natural floor, rather than assumed. -/
theorem quantile_between {s : ℕ} (hs : 0 < s) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) (hgap : 1 / (s : ℝ) < v - u) :
    ∃ j : Fin (s + 1), 0 < j.val ∧ j.val < s ∧ u < (j.val : ℝ) / s ∧ (j.val : ℝ) / s < v := by
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hstep : 0 < 1 / (s : ℝ) := by positivity
  have huone : u < 1 := by linarith
  have hsu : 0 ≤ (s : ℝ) * u := mul_nonneg hsreal.le hu
  let j : ℕ := ⌊(s : ℝ) * u⌋₊ + 1
  have hjle : j ≤ s := by
    dsimp [j]
    have hfloor : ⌊(s : ℝ) * u⌋₊ < s := (Nat.floor_lt hsu).mpr (by nlinarith)
    omega
  have hlow : u < (j : ℝ) / s := by
    apply (lt_div_iff₀ hsreal).mpr
    have h := Nat.lt_floor_add_one ((s : ℝ) * u)
    dsimp [j]
    push_cast
    nlinarith
  have hhigh : (j : ℝ) / s < v := by
    apply (div_lt_iff₀ hsreal).mpr
    have hfloor := Nat.floor_le hsu
    have hscaled := (div_lt_iff₀ hsreal).mp (show 1 / (s : ℝ) < v - u from hgap)
    dsimp [j]
    push_cast
    nlinarith
  have hjlt : j < s := by
    by_contra hn
    have hj : j = s := le_antisymm hjle (le_of_not_gt hn)
    rw [hj, div_self hsreal.ne'] at hhigh
    linarith
  exact ⟨⟨j, Nat.lt_succ_of_le hjle⟩, by dsimp [j]; omega, hjlt, hlow, hhigh⟩

theorem cumulative_cell_gap {m s : ℕ} (hs : 0 < s) (F : ℝ → ℝ) (hF : Monotone F)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts)
    (hrange : ∀ i, 0 ≤ F (cuts i) ∧ F (cuts i) ≤ 1)
    (hquantile : ∀ j : Fin (s + 1), 0 < j.val → j.val < s →
      ∃ c : Fin (m + 2), F (cuts c) = (j.val : ℝ) / s)
    (i : Fin (m + 1)) : F (cuts i.succ) - F (cuts i.castSucc) ≤ 1 / (s : ℝ) := by
  by_contra hn
  obtain ⟨j, hjpos, hjlt, hlo, hhi⟩ := quantile_between hs
    (F (cuts i.castSucc)) (F (cuts i.succ))
    (hrange i.castSucc).1 (hrange i.succ).2 (lt_of_not_ge hn)
  obtain ⟨c, hc⟩ := hquantile j hjpos hjlt
  have hleft : cuts i.castSucc < cuts c := by
    by_contra hn
    have h := hF (le_of_not_gt hn)
    rw [hc] at h
    linarith
  have hright : cuts c < cuts i.succ := by
    by_contra hn
    have h := hF (le_of_not_gt hn)
    rw [hc] at h
    linarith
  exact no_grid_point_between cuts hmono i c ⟨hleft, hright⟩

/-- The logical cell has small normalized physical mass. Old buffer joins
do not enter the number of quantile or sampled cells. -/
theorem normalized_cell_mass_le {m s : ℕ} (hs : 0 < s) (μ : Measure ℝ)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (buffer : Set ℝ) (hbuffer : MeasurableSet buffer) (hpositive : 0 < μ.real buffer)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts)
    (hquantile : ∀ j : Fin (s + 1), 0 < j.val → j.val < s →
      ∃ c : Fin (m + 2), cdf (cond μ buffer) (cuts c) = (j.val : ℝ) / s)
    (i : Fin (m + 1)) : μ.real (cell buffer cuts i) / μ.real buffer ≤ 1 / (s : ℝ) := by
  let : IsProbabilityMeasure (cond μ buffer) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero μ buffer hpositive)
  have h := cumulative_cell_gap hs (cdf (cond μ buffer)) (monotone_cdf _) cuts hmono
    (fun c => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩) hquantile i
  rw [normalized_cdf μ buffer hpositive, normalized_cdf μ buffer hpositive,
    ← sub_div, ← cell_mass_prefix μ buffer hbuffer cuts hmono] at h
  exact h

end EnvyFreeResearch.Full.UpperQuantileBounds
