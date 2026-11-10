import EnvyFreeResearch.Full.RefinedUpperPeelingRecorded
import EnvyFreeResearch.Full.UpperLogicalPreparationMass

/-! Actual retained domain after deterministic removal of selected parents. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperCommonGrid UpperLogicalPreparation Chores
open scoped Classical BigOperators unitInterval
variable {Parent : Type*} [DecidableEq Parent]

/-- This deterministic mask retains exactly the parents not selected by
peeling. It reuses the recorded filtering implementation without random labels. -/
def retentionLabels (removed : Finset Parent) (p : Parent) : I := if p ∈ removed then 1 else 0

@[simp] lemma retentionLabels_le_zero (removed : Finset Parent) (p : Parent) :
    retentionLabels removed p ≤ 0 ↔ p ∉ removed := by
  by_cases hp : p ∈ removed <;> simp [retentionLabels,hp]

@[simp] lemma retention_mark (removed : Finset Parent) (p : Parent) :
    UpperReserve.mark 0 (retentionLabels removed p) = if p ∈ removed then 0 else 1 := by
  by_cases hp : p ∈ removed <;> simp [UpperReserve.mark,retentionLabels,hp]

lemma retained_value_identity [Fintype Parent] (weights : Parent → ℝ) (removed : Finset Parent)
    (hnorm : ∑ p, weights p = 1) :
    UpperReserve.reserveValue weights 0 (retentionLabels removed) = 1-∑ p ∈ removed, weights p := by
  have hsum : UpperReserve.reserveValue weights 0 (retentionLabels removed) + ∑ p ∈ removed, weights p =
      ∑ p, weights p := by
    have hrem : (∑ p ∈ removed, weights p) = ∑ p, if p ∈ removed then weights p else 0 := by
      simp [← Finset.sum_filter]
    rw [UpperReserve.reserveValue,hrem,← Finset.sum_add_distrib]
    simp only [retention_mark]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ removed <;> simp [hp]
  linarith

lemma retained_value_lower [Fintype Parent] (weights : Parent → ℝ) (removed : Finset Parent)
    (hnorm : ∑ p, weights p = 1) (eta : ℝ) (hsmall : ∀ p ∈ removed, weights p ≤ eta) :
    1-(removed.card : ℝ)*eta ≤ UpperReserve.reserveValue weights 0 (retentionLabels removed) := by
  rw [retained_value_identity weights removed hnorm]
  have hle : (∑ p ∈ removed, weights p) ≤ (removed.card : ℝ)*eta := by
    calc
      _ ≤ ∑ _p ∈ removed, eta := Finset.sum_le_sum hsmall
      _ = _ := by simp
  linarith

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def retainedState (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (removed : Finset (Fin (count (Agent := Agent) q + 1))) : State n :=
  reserveState policy active origin q m draw 0 (retentionLabels removed)

lemma retainedState_history (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (removed : Finset (Fin (count (Agent := Agent) q + 1))) :
    (retainedState policy active origin q m draw removed).history =
      (UpperGridCache.aligned policy active origin q m draw).history := rfl

section Physical
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem retainedState_domain (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1))) :
    domain (retainedState policy active origin q m draw removed).cells =
      ⋃ p, if p ∉ removed then UpperRecordedQuantiles.logicalCells policy active origin q p else ∅ := by
  rw [retainedState,reserveState_domain μ policy hpolicy active origin hgood hpositive]
  unfold labelledUnion
  apply iUnion_congr
  intro p
  by_cases hp : p ∈ removed <;> simp [retentionLabels,hp]

theorem retainedState_wellFormed (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1))) :
    WellFormed μ (retainedState policy active origin q m draw removed) :=
  reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw 0 (retentionLabels removed)

/-- Every physical row loses at most the number of selected parents times
the coarse-cell cap. No probabilistic mass check or independence is used. -/
theorem retainedState_mass_lower (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1))) (a : Agent) :
    1-(removed.card : ℝ)/(q+1 : ℝ) ≤
      total (retainedState policy active origin q m draw removed) (active a)/total origin (active a) := by
  rw [retainedState,reserveState_normalized_total μ policy hpolicy active origin hgood hpositive]
  have h := retained_value_lower (coarseWeights μ policy active origin q a) removed
    (coarseWeights_normalized μ policy hpolicy active origin hgood hpositive q a)
    (1/(q+1 : ℝ)) (fun p _ => coarseWeights_small μ policy hpolicy active origin hgood hpositive q a p)
  simpa only [div_eq_mul_inv,one_mul] using h

end Physical

lemma retentionLabels_measurable {P : Type*} [DecidableEq P] [Countable P]
    [MeasurableSpace P] [MeasurableSingletonClass P] :
    Measurable (fun removed : Finset P => retentionLabels removed) := by
  apply Measurable.of_eval
  intro p
  exact measurable_of_countable (fun removed : Finset P => retentionLabels removed p)

set_option maxHeartbeats 400000 in
lemma retainedState_measurable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (active : Agent → Fin n) (q m : ℕ) :
    Measurable (fun z : (State n × (Fin m → Agent × I)) × Finset (Fin (count (Agent := Agent) q + 1)) =>
      retainedState policy active z.1.1 q m z.1.2 z.2) := by
  let P := Fin (count (Agent := Agent) q + 1)
  have hlabels : Measurable (fun removed : Finset P => retentionLabels removed) := retentionLabels_measurable
  have hh := (reserveState_measurable policy hpolicy active q m 0).comp
    (measurable_fst.prodMk (hlabels.comp measurable_snd))
  exact hh

end EnvyFreeResearch.Full.RefinedUpperPreparation
