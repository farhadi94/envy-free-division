import EnvyFreeResearch.Full.UpperLogicalPreparationSupport
import EnvyFreeResearch.Full.UpperCorrectionSetup

/-!
# Actual reserve mass checks and the normalized reserve-cell bound

The final state's cached total is exactly the fixed coarse-label weighted
sum. Its failure probability follows from the original independent labels.
Passing the lower mass check gives the small-cell bound needed by rounding.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridCells
  UpperLogicalCells UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperCommonGrid Chores

variable {Parent : Type*} [Fintype Parent]

theorem labelledUnion_mass (μ : Measure ℝ) [IsFiniteMeasure μ] (coarse : Parent → Set ℝ)
    (hmeas : ∀ p, MeasurableSet (coarse p)) (hdis : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (theta : I) (labels : Parent → I) :
    μ.real (labelledUnion coarse theta labels) =
      UpperReserve.reserveValue (fun p => μ.real (coarse p)) theta labels := by
  unfold labelledUnion UpperReserve.reserveValue
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro p _
    simp only [UpperReserve.mark, Set.indicator_apply, mem_Iic]
    split_ifs <;> simp
  · intro p q hpq
    dsimp only [Function.onFun]
    split_ifs <;> simp [hdis hpq]
  · intro p
    split_ifs
    · exact hmeas p
    · exact MeasurableSet.empty

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

/-- Analytic identification of the coarse cache, fixed before fine sampling. -/
def coarseWeights (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (origin : State n) (q : ℕ) (a : Agent) (p : Fin (count (Agent := Agent) q + 1)) : ℝ :=
  (μ (active a)).real (UpperRecordedQuantiles.logicalCells policy active origin q p) /
    (μ (active a)).real (domain origin.cells)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem coarseWeights_nonnegative (q : ℕ) (a : Agent) (p : Fin (count (Agent := Agent) q + 1)) :
    0 ≤ coarseWeights μ policy active origin q a p :=
  div_nonneg measureReal_nonneg (hpositive a).le

theorem coarseWeights_small (q : ℕ) (a : Agent) (p : Fin (count (Agent := Agent) q + 1)) :
    coarseWeights μ policy active origin q a p ≤ 1 / (q + 1 : ℝ) :=
  UpperRecordedQuantiles.logical_cells_small μ policy hpolicy active origin hgood hpositive q a p

theorem coarseWeights_normalized (q : ℕ) (a : Agent) :
    (∑ p, coarseWeights μ policy active origin q a p) = 1 := by
  have hc := UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q
  simp only [coarseWeights, ← Finset.sum_div]
  rw [← measureReal_iUnion_fintype hc.1 hc.2.1, hc.2.2]
  exact div_self (hpositive a).ne'

/-- The mass check is a computation on the actual full-history state; its
value is exactly the coarse-label sum fixed independently of fine samples. -/
theorem reserveState_normalized_total (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) (a : Agent) :
    total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a) =
      UpperReserve.reserveValue (coarseWeights μ policy active origin q a) theta labels := by
  have hc := UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q
  rw [total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels),
    total_correct μ origin hgood, reserveState_domain μ policy hpolicy active origin hgood hpositive q m draw theta labels,
    labelledUnion_mass _ _ hc.2.1 hc.1]
  simp only [UpperReserve.reserveValue, Finset.sum_div, coarseWeights]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- All active mass-check failures are bounded on the original label law.
The sampler is not conditioned on passing these checks. -/
theorem reserveState_mass_probability (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (htheta : 0 < (theta : ℝ)) :
    UpperReserve.labelLaw {labels | ∃ a,
      total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a) < (theta : ℝ) / 2 ∨
      3 * (theta : ℝ) / 2 < total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a)} ≤
        ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ))) := by
  simp_rw [reserveState_normalized_total μ policy hpolicy active origin hgood hpositive]
  have h := UpperReserve.any_badMass_probability (coarseWeights μ policy active origin q) theta
    (1 / (q + 1 : ℝ)) htheta
    (coarseWeights_nonnegative μ policy hpolicy active origin hgood hpositive q)
    (coarseWeights_small μ policy hpolicy active origin hgood hpositive q)
    (coarseWeights_normalized μ policy hpolicy active origin hgood hpositive q)
  have hevent : {labels | ∃ a,
      UpperReserve.reserveValue (coarseWeights μ policy active origin q a) theta labels < (theta : ℝ) / 2 ∨
      3 * (theta : ℝ) / 2 < UpperReserve.reserveValue (coarseWeights μ policy active origin q a) theta labels} =
      ⋃ a, UpperReserve.badMass (coarseWeights μ policy active origin q a) theta := by
    ext labels
    simp only [mem_ofPred_eq, mem_iUnion, UpperReserve.badMass]
  rw [hevent]
  convert h using 1
  congr 1
  field_simp

end Correctness

/-- Pure normalization arithmetic used after the reserve lower-mass check. -/
theorem renormalized_small (mass buffer reserve eta theta : ℝ)
    (hbuffer : 0 < buffer) (htheta : 0 < theta) (heta : 0 ≤ eta)
    (hsmall : mass / buffer ≤ eta) (hreserve : theta / 2 * buffer ≤ reserve) :
    mass / reserve ≤ 2 * eta / theta := by
  have hden : 0 < theta / 2 * buffer := mul_pos (div_pos htheta (by norm_num)) hbuffer
  have hpos : 0 < reserve := hden.trans_le hreserve
  calc
    mass / reserve ≤ (eta * buffer) / reserve := div_le_div_of_nonneg_right ((div_le_iff₀ hbuffer).mp hsmall) hpos.le
    _ ≤ (eta * buffer) / (theta / 2 * buffer) :=
      div_le_div_of_nonneg_left (mul_nonneg heta hbuffer.le) hden hreserve
    _ = 2 * eta / theta := by field_simp

section CacheBound

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

/-- The actual cached reserve table has the required `2/(theta*(q+1))`
small-cell bound whenever the raw reserve lower-mass check passes. -/
theorem reserveState_table_small (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (htheta : 0 < (theta : ℝ)) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hlower : ∀ a, (theta : ℝ) / 2 * (μ (active a)).real (domain origin.cells) ≤
      (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells))
    (a : Agent) (e : Fin (count (Agent := Agent) q + m + 1)) :
    cachedMass (reserveState policy active origin q m draw theta labels)
        (UpperGridMerge.cuts policy active origin q m draw) (active a) e /
      total (reserveState policy active origin q m draw theta labels) (active a) ≤
        2 / ((theta : ℝ) * (q + 1 : ℝ)) := by
  rw [reserveState_cachedMass μ policy hpolicy active origin hgood hpositive,
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)]
  split_ifs
  · have h := renormalized_small _ _ _ (1 / (q + 1 : ℝ)) (theta : ℝ)
      (hpositive a) htheta (by positivity)
      (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw a e)
      (hlower a)
    convert h using 1
    field_simp
  · simp only [zero_div]
    positivity

end CacheBound

end EnvyFreeResearch.Full.UpperLogicalPreparation
