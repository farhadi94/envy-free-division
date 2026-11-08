import EnvyFreeResearch.Full.UpperGridInterpolation
import EnvyFreeResearch.Full.UpperLogicalPrefix
import EnvyFreeResearch.Full.UpperEnvelope

/-!
# Physical finite-union interpretation of grid interpolation

The cumulative coordinate is actual volume on the current recorded buffer.
Finite interval-union geometry proves flat-cell compatibility for every
atomless row, including singular rows. Logical cells may cross old joins.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperRecordedDomain UpperLogicalCells UpperLogicalCellNull UpperLogicalPrefix UpperSortedGrid
  UpperGridSensitivity

def domainCumulative (μ : Measure ℝ) (cs : List Component) (x : ℝ) : ℝ :=
  μ.real (domain cs ∩ Iic x)

theorem domainCumulative_measurable (μ : Measure ℝ) [SFinite μ] (cs : List Component) :
    Measurable (domainCumulative μ cs) := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 ∈ domain cs ∧ p.2 ≤ p.1} :=
    ((domain_measurable cs).preimage measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
  exact (measurable_measure_prodMk_left (ν := μ) hm).ennreal_toReal

theorem domainCumulative_monotone (μ : Measure ℝ) (cs : List Component)
    (hfinite : μ (domain cs) ≠ ∞) : Monotone (domainCumulative μ cs) := by
  intro x y hxy
  exact measureReal_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr hxy))
    (measure_ne_top_of_subset inter_subset_left hfinite)

theorem domainCumulative_zero (μ : Measure ℝ) [NullSingletonClass μ] (cs : List Component) :
    domainCumulative μ cs 0 = 0 := by
  have hsub : domain cs ∩ Iic (0 : ℝ) ⊆ {0} := by
    intro x hx
    exact mem_singleton_iff.mpr (le_antisymm hx.2 (domain_subset_unit cs hx.1).1)
  have hz : μ (domain cs ∩ Iic (0 : ℝ)) = 0 := measure_mono_null hsub (by simp)
  exact congrArg ENNReal.toReal hz

theorem domain_volume_finite (cs : List Component) : volume (domain cs) ≠ ∞ :=
  measure_ne_top_of_subset (domain_subset_unit cs)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- Prefix subtraction only needs finiteness on the physical domain. -/
theorem physical_cell_mass {m : ℕ} (μ : Measure ℝ) [NullSingletonClass μ]
    (cs : List Component) (hfinite : μ (domain cs) ≠ ∞)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) (e : Fin (m + 1)) :
    μ.real (cell (domain cs) cuts e) =
      domainCumulative μ cs (cuts e.succ) - domainCumulative μ cs (cuts e.castSucc) := by
  let ν := μ.restrict (domain cs)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfinite
  have h := cell_mass_prefix ν (domain cs) (domain_measurable cs) cuts hmono e
  have hc : cell (domain cs) cuts e ∩ domain cs = cell (domain cs) cuts e :=
    inter_eq_left.mpr (cell_subset _ _ _)
  have hp (r : ℝ) : (domain cs ∩ Iic r) ∩ domain cs = domain cs ∩ Iic r :=
    inter_eq_left.mpr inter_subset_left
  simpa only [ν, measureReal_restrict_apply' (domain_measurable cs), hc, hp, domainCumulative] using h

variable {Row : Type*} [Fintype Row] [Nonempty Row]

def normalizedCumulative (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (cs : List Component) :
    Row → ℝ → ℝ := fun i x => domainCumulative (μ i) cs x / normalizer i

def physicalRows {m : ℕ} (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (cs : List Component) (cuts : Fin (m + 2) → ℝ) : Row → Fin (m + 1) → ℝ :=
  fun i e => (μ i).real (cell (domain cs) cuts e) / normalizer i

variable (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem normalizedCumulative_measurable (normalizer : Row → ℝ) (cs : List Component) (i : Row) :
    Measurable (normalizedCumulative μ normalizer cs i) :=
  (domainCumulative_measurable (μ i) cs).div_const _

/-- No absolute-continuity assumption is used. A zero-volume interval in a
finite component domain has zero mass for every atomless row. -/
theorem normalizedCumulative_flat (normalizer : Row → ℝ) (cs : List Component) :
    FlatCompatible (normalizedCumulative μ normalizer cs) (domainCumulative volume cs) := by
  intro i a b hab hflat
  let cuts : Fin 2 → ℝ := ![a, b]
  have hm : Monotone cuts := by
    apply Fin.monotone_iff_le_succ.mpr
    intro e
    fin_cases e
    exact hab
  have hvol := physical_cell_mass volume cs (domain_volume_finite cs) cuts hm 0
  have hz : volume.real (cell (domain cs) cuts 0) = 0 := by
    simpa [cuts, hflat] using hvol
  have hr := cell_real_null (μ i) cs cuts 0 hz
  rw [physical_cell_mass (μ i) cs (measure_ne_top _ _) cuts hm 0] at hr
  have he : domainCumulative (μ i) cs a = domainCumulative (μ i) cs b := by
    have hr' : domainCumulative (μ i) cs b - domainCumulative (μ i) cs a = 0 := by
      simpa [cuts] using hr
    exact (sub_eq_zero.mp hr').symm
  simp only [normalizedCumulative, he]

theorem physicalRows_eq_linearRows {m : ℕ} (normalizer : Row → ℝ) (cs : List Component)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) :
    physicalRows μ normalizer cs cuts = linearRows (normalizedCumulative μ normalizer cs) cuts := by
  funext i e
  rw [physicalRows, physical_cell_mass (μ i) cs (measure_ne_top _ _) cuts hmono e]
  exact sub_div _ _ _

/-- The cell-sum interpolant is exactly the existing physical envelope
estimate on the same logical cells and cumulative-volume coordinates. -/
theorem linearEstimate_sub_eq_envelope {m : ℕ} (normalizer : Row → ℝ) (cs : List Component)
    (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts) (hzero : cuts 0 = 0) (z : ℝ) (i j : Row) :
    linearEstimate (normalizedCumulative μ normalizer cs i) (domainCumulative volume cs) cuts z -
      linearEstimate (normalizedCumulative μ normalizer cs j) (domainCumulative volume cs) cuts z =
      UpperEnvelope.estimate (physicalRows μ normalizer cs cuts)
        (UpperEnvelope.uniformCells (cell (domain cs) cuts)) i j (Iic z) := by
  have hbase (k : Row) : normalizedCumulative μ normalizer cs k (cuts 0) = 0 := by
    rw [hzero, normalizedCumulative, domainCumulative_zero, zero_div]
  rw [linearEstimate, linearEstimate, hbase, hbase, zero_add, zero_add,
    ← Finset.sum_sub_distrib, UpperEnvelope.uniform_estimate_formula _ _
      (cell_measurable _ (domain_measurable cs) cuts)]
  apply Finset.sum_congr rfl
  intro e _
  have hr := congrFun (congrFun (physicalRows_eq_linearRows μ normalizer cs cuts hmono) i) e
  have hs := congrFun (congrFun (physicalRows_eq_linearRows μ normalizer cs cuts hmono) j) e
  rw [cell_volume_prefix cs cuts hmono e z,
    physical_cell_mass volume cs (domain_volume_finite cs) cuts hmono e]
  change _ = (physicalRows μ normalizer cs cuts i e - physicalRows μ normalizer cs cuts j e) * _
  rw [hr, hs]
  dsimp only [linearRows, cellFraction, domainCumulative]
  ring

/-- The integrated estimate specialized to actual normalized atomless
physical rows on a recorded finite union and its true volume coordinate. -/
theorem integrated_physical_linear_le {b m : ℕ} (normalizer : Row → ℝ) (cs : List Component)
    (permanent : Fin b → ℝ) (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw]
    [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1) :
    (∫ samples : Fin m → ℝ, ∫ test,
      linearMaximum (normalizedCumulative μ normalizer cs) (domainCumulative volume cs)
        (sorted (augmented permanent samples)) test ∂sampleLaw
      ∂Measure.pi (fun _ : Fin m => sampleLaw)) ≤
        2 * ((Fintype.card Row : ℝ) - 1) / (m + 1 : ℕ) :=
  integrated_linear_interpolation_le _ (normalizedCumulative_measurable μ normalizer cs)
    _ (domainCumulative_monotone volume cs (domain_volume_finite cs))
    (domainCumulative_measurable volume cs) (normalizedCumulative_flat μ normalizer cs)
    permanent sampleLaw hsupport

end EnvyFreeResearch.Full.UpperGridInterpolation
