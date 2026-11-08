import EnvyFreeResearch.Full.UpperGridInterpolationPhysical
import EnvyFreeResearch.Full.UpperGridInterpolationLinearMeasurable

/-! Final interpolation estimate for the actual logical-cell envelope. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperRecordedDomain UpperLogicalCells UpperSortedGrid UpperGridSensitivity

variable {Row : Type*} [Fintype Row] [Nonempty Row]

def physicalError {n : ℕ} (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (cs : List Component)
    (cuts : Fin (n + 2) → ℝ) (z : ℝ) (i j : Row) : ℝ :=
  |(normalizedCumulative μ normalizer cs i z - normalizedCumulative μ normalizer cs j z) -
    UpperEnvelope.estimate (physicalRows μ normalizer cs cuts)
      (UpperEnvelope.uniformCells (cell (domain cs) cuts)) i j (Iic z)|

def physicalMaximum {n : ℕ} (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (cs : List Component)
    (cuts : Fin (n + 2) → ℝ) (z : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Row × Row =>
    physicalError μ normalizer cs cuts z ij.1 ij.2 /
      (distance (physicalRows μ normalizer cs cuts) ij.1 ij.2 +
        physicalError μ normalizer cs cuts z ij.1 ij.2))

variable (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem linearMaximum_eq_physical {n : ℕ} (normalizer : Row → ℝ) (cs : List Component)
    (cuts : Fin (n + 2) → ℝ) (hmono : Monotone cuts) (hzero : cuts 0 = 0) (z : ℝ) :
    linearMaximum (normalizedCumulative μ normalizer cs) (domainCumulative volume cs) cuts z =
      physicalMaximum μ normalizer cs cuts z := by
  unfold linearMaximum physicalMaximum
  congr 1
  funext ij
  rw [linearError, linearEstimate_sub_eq_envelope μ normalizer cs cuts hmono hzero,
    ← physicalRows_eq_linearRows μ normalizer cs cuts hmono]
  rfl

/-- Joint Borel error on varying valid logical grids and varying test
endpoints. The physical buffer and original rows are fixed before sampling. -/
theorem physicalMaximum_measurable {X : Type*} [MeasurableSpace X] {n : ℕ}
    (normalizer : Row → ℝ) (cs : List Component) (cuts : X → Fin (n + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (hmono : ∀ z, Monotone (cuts z))
    (hzero : ∀ z, cuts z 0 = 0) (test : X → ℝ) (htest : Measurable test) :
    Measurable (fun z => physicalMaximum μ normalizer cs (cuts z) (test z)) := by
  convert linearMaximum_measurable (normalizedCumulative μ normalizer cs)
    (normalizedCumulative_measurable μ normalizer cs) (domainCumulative volume cs)
    (domainCumulative_measurable volume cs) cuts hcuts test htest using 1
  funext z
  exact (linearMaximum_eq_physical μ normalizer cs (cuts z) (hmono z) (hzero z) (test z)).symm

theorem augmented_nonneg {b m : ℕ} (permanent : Fin b → ℝ) (samples : Fin m → ℝ)
    (hpermanent : ∀ i, 0 ≤ permanent i) (hsamples : ∀ i, 0 ≤ samples i) :
    ∀ j, 0 ≤ augmented permanent samples j := by
  intro j
  refine Fin.cases (by simp [augmented]) (fun q => ?_) j
  refine Fin.lastCases (by simp [augmented]) (fun q => ?_) q
  refine Fin.addCases (fun i => ?_) (fun i => ?_) q
  · simpa only [augmented, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_left] using hpermanent i
  · simpa only [augmented, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_right] using hsamples i

/-- The manuscript's integrated interpolation estimate for the existing
physical `UpperEnvelope.estimate`, the original immutable logical grid, and
all pairwise zero-denominator cases. The original physical joins never
enter the sampled-grid index set. -/
theorem integrated_envelope_interpolation_le {b m : ℕ} (normalizer : Row → ℝ) (cs : List Component)
    (permanent : Fin b → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1) :
    (∫ samples : Fin m → ℝ, ∫ test,
      physicalMaximum μ normalizer cs (sorted (augmented permanent samples)) test ∂sampleLaw
      ∂Measure.pi (fun _ : Fin m => sampleLaw)) ≤
        2 * ((Fintype.card Row : ℝ) - 1) / (m + 1 : ℕ) := by
  have hsamples : ∀ᵐ samples ∂Measure.pi (fun _ : Fin m => sampleLaw), ∀ i, 0 ≤ samples i := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => sampleLaw) i).quasiMeasurePreserving.ae
      (hsupport.mono (fun _ h => h.1))
  have heq : (fun samples : Fin m → ℝ => ∫ test,
      physicalMaximum μ normalizer cs (sorted (augmented permanent samples)) test ∂sampleLaw) =ᵐ[
        Measure.pi (fun _ : Fin m => sampleLaw)]
      (fun samples : Fin m → ℝ => ∫ test,
        linearMaximum (normalizedCumulative μ normalizer cs) (domainCumulative volume cs)
          (sorted (augmented permanent samples)) test ∂sampleLaw) := by
    filter_upwards [hsamples] with samples hsamples
    have hzero : sorted (augmented permanent samples) 0 = 0 :=
      first_eq_zero _ (augmented_nonneg permanent samples hpermanent hsamples) ⟨0, by simp [augmented]⟩
    apply integral_congr_ae
    exact ae_of_all _ (fun test => (linearMaximum_eq_physical μ normalizer cs _
      (sorted_monotone _) hzero test).symm)
  rw [integral_congr_ae heq]
  exact integrated_physical_linear_le μ normalizer cs permanent sampleLaw hsupport

end EnvyFreeResearch.Full.UpperGridInterpolation
