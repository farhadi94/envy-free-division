import EnvyFreeResearch.Full.IntervalOracle

/-!
Signed valuations given by actual integrable real densities. Every row yields
an atomless signed measure and a continuous interval-oracle profile. The
finite frontier update is built from density restrictions and constant cells.
-/

noncomputable section
namespace EnvyFreeResearch.Full.MixedDensity

open Set MeasureTheory IntervalOracle TranscriptAdversary
open scoped ENNReal

structure Row where
  density : ℝ → ℝ
  integrable : Integrable density volume

namespace Row

def cumulative (R : Row) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, R.density t

def signedMeasure (R : Row) : SignedMeasure ℝ := volume.withDensityᵥ R.density

theorem cumulative_continuous (R : Row) : Continuous R.cumulative :=
  R.integrable.continuous_primitive 0

@[simp] theorem cumulative_zero (R : Row) : R.cumulative 0 = 0 := by
  simp [cumulative]

theorem signedMeasure_apply (R : Row) (S : Set ℝ) (hS : MeasurableSet S) :
    R.signedMeasure S = ∫ t in S, R.density t :=
  withDensityᵥ_apply R.integrable hS

@[simp] theorem signedMeasure_singleton (R : Row) (x : ℝ) :
    R.signedMeasure {x} = 0 := by
  rw [signedMeasure_apply R _ (measurableSet_singleton x)]
  simp

theorem signedMeasure_absolutelyContinuous (R : Row) :
    R.signedMeasure ≪ᵥ volume.toENNRealVectorMeasure :=
  volume.withDensityᵥ_absolutelyContinuous R.density

/-- The cumulative difference is the value of the actual physical interval. -/
theorem interval_value (R : Row) {a b : ℝ} (hab : a ≤ b) :
    R.cumulative b - R.cumulative a = R.signedMeasure (Ioc a b) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := a) (c := b) R.integrable.intervalIntegrable
    R.integrable.intervalIntegrable
  rw [signedMeasure_apply R _ measurableSet_Ioc]
  rw [intervalIntegral.integral_of_le hab] at h
  unfold cumulative
  linarith

/-- Adding densities preserves actual signed-measure semantics. -/
def add (R S : Row) : Row := ⟨fun x => R.density x + S.density x, R.integrable.add S.integrable⟩

@[simp] theorem cumulative_add (R S : Row) (x : ℝ) :
    (R.add S).cumulative x = R.cumulative x + S.cumulative x := by
  exact intervalIntegral.integral_add R.integrable.intervalIntegrable S.integrable.intervalIntegrable

/-- A finite constant-density cell; the density may have either sign. -/
def cell (a b d : ℝ) : Row where
  density := (Ioc a b).indicator (fun _ => d)
  integrable := (integrableOn_const (by simp [Real.volume_Ioc] : volume (Ioc a b) ≠ ∞)).integrable_indicator
    measurableSet_Ioc

theorem cumulative_cell (a b d x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (cell a b d).cumulative x = d * max (min x b - a) 0 := by
  unfold cumulative cell
  rw [intervalIntegral.integral_of_le hx, setIntegral_indicator measurableSet_Ioc]
  rw [Ioc_inter_Ioc, max_eq_right ha]
  rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
  ring

/-- Keep exactly the old prefix density. -/
def prefixRow (R : Row) (l : ℝ) : Row where
  density := (Ioc 0 l).indicator R.density
  integrable := R.integrable.indicator measurableSet_Ioc

theorem cumulative_prefix (R : Row) (l x : ℝ) (hl : 0 ≤ l) (hx : 0 ≤ x) :
    (R.prefixRow l).cumulative x = R.cumulative (min x l) := by
  unfold cumulative prefixRow
  rw [intervalIntegral.integral_of_le hx, setIntegral_indicator measurableSet_Ioc]
  rw [Ioc_inter_Ioc, max_self, intervalIntegral.integral_of_le (le_min hx hl)]

def rebuilt (R : Row) (l h d : ℝ) : Row :=
  (R.prefixRow l).add ((cell l h d).add
    (cell h 1 ((1 - (R.cumulative l + d * (h - l))) / (1 - h))))

theorem cumulative_rebuilt (R : Row) (l h d x : ℝ)
    (hl : 0 ≤ l) (hlh : l < h) (_hh : h < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    (R.rebuilt l h d).cumulative x = rebuild R.cumulative l h d x := by
  have hh0 : 0 ≤ h := le_trans hl hlh.le
  unfold rebuilt
  rw [cumulative_add, cumulative_add, cumulative_prefix R l x hl hx.1,
    cumulative_cell l h d x hl hx.1,
    cumulative_cell h 1 _ x hh0 hx.1, min_eq_left hx.2]
  by_cases hxl : x ≤ l
  · have hxh : x ≤ h := hxl.trans hlh.le
    rw [min_eq_left hxl, min_eq_left hxh,
      max_eq_right (sub_nonpos.mpr hxl), max_eq_right (sub_nonpos.mpr hxh),
      rebuild_prefix hxl]
    ring
  · have hlx : l ≤ x := (lt_of_not_ge hxl).le
    rw [min_eq_right hlx]
    by_cases hxh : x ≤ h
    · rw [min_eq_left hxh, max_eq_left (sub_nonneg.mpr hlx),
        max_eq_right (sub_nonpos.mpr hxh), rebuild_new_cell (lt_of_not_ge hxl) hxh]
      ring
    · have hhx : h ≤ x := (lt_of_not_ge hxh).le
      rw [min_eq_right hhx, max_eq_left (sub_nonneg.mpr hlh.le),
        max_eq_left (sub_nonneg.mpr hhx)]
      simp only [rebuild, hxl, ite_false, hxh]
      ring

/-- A concrete density update inherits the strict terminal barrier. -/
theorem rebuilt_terminal_ceiling (R : Row) {l h d : ℝ}
    (hR : TerminalCeiling R.cumulative) (hl : 0 ≤ l)
    (hlh : l < h) (hh : h < 1) (hd : d ≤ 0) :
    TerminalCeiling (R.rebuilt l h d).cumulative := by
  have hb := rebuild_terminal_ceiling hR hl hlh hh hd
  constructor
  · rw [cumulative_rebuilt R l h d 1 hl hlh hh (by simp)]
    exact hb.1
  · intro x hx
    rw [cumulative_rebuilt R l h d x hl hlh hh ⟨hx.1, hx.2.le⟩]
    exact hb.2 x hx


/-- Prefix densities are preserved pointwise away from the null endpoint. -/
theorem rebuilt_density_prefix (R : Row) {l h d x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) l) (hlh : l ≤ h) :
    (R.rebuilt l h d).density x = R.density x := by
  have hnew : x ∉ Ioc l h := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  have htail : x ∉ Ioc h 1 := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  simp [rebuilt, add, prefixRow, cell, hx, hnew, htail]

/-- The new resolved cell has exactly the requested constant density. -/
theorem rebuilt_density_cell (R : Row) {l h d x : ℝ}
    (hx : x ∈ Ioc l h) : (R.rebuilt l h d).density x = d := by
  have hold : x ∉ Ioc (0 : ℝ) l := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  have htail : x ∉ Ioc h 1 := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  simp [rebuilt, add, prefixRow, cell, hx, hold, htail]

/-- The compensating final tail has constant density. -/
theorem rebuilt_density_tail (R : Row) {l h d x : ℝ}
    (hx : x ∈ Ioc h (1 : ℝ)) (hlh : l ≤ h) :
    (R.rebuilt l h d).density x =
      (1 - (R.cumulative l + d * (h - l))) / (1 - h) := by
  have hold : x ∉ Ioc (0 : ℝ) l := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  have hnew : x ∉ Ioc l h := by intro hy; linarith [hx.1, hx.2, hy.1, hy.2]
  simp [rebuilt, add, prefixRow, cell, hx, hold, hnew]

end Row

def toProfile {Agent : Type*} (R : Agent → Row) : Profile Agent where
  cumulative i := (R i).cumulative
  continuous i := (R i).cumulative_continuous
  zero i := (R i).cumulative_zero

end EnvyFreeResearch.Full.MixedDensity
