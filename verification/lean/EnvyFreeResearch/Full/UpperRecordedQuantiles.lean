import EnvyFreeResearch.Full.UpperRecordedGrid
import EnvyFreeResearch.Full.UpperCommonGrid

/-!
# Recorded common quantiles without profile access in the program

This composes the deterministic quantile schedule with the actual recorded
state executor. All query targets and cell masses come from the transcript;
normalized physical guarantees are derived from the truthful-cache invariant.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRecordedQuantiles

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperQuantileExecution UpperLogicalCells Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

abbrev count (q : ℕ) := Fintype.card (Agent × Fin q)

def run (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    (Fin (count (Agent := Agent) q) → ℝ) × State n :=
  UpperRecordedGrid.execute policy active origin _ (schedule q)

def cuts (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    Fin (count (Agent := Agent) q + 2) → ℝ := UpperCommonGrid.grid (run policy active origin q).1

def logicalCells (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    Fin (count (Agent := Agent) q + 1) → Set ℝ := cell (domain origin.cells) (cuts policy active origin q)

theorem count_eq (q : ℕ) : count (Agent := Agent) q = Fintype.card Agent * q := by
  simp [count]

theorem run_domain (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    domain (run policy active origin q).2.cells = domain origin.cells :=
  UpperRecordedGrid.execute_domain policy active origin _ _

theorem query_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    (run policy active origin q).2.history.length ≤
      origin.history.length + (Fintype.card Agent * q) * (n + 1) := by
  have h := UpperRecordedGrid.query_bound policy active origin (count (Agent := Agent) q) (schedule q)
  simpa only [run, count, Fintype.card_prod, Fintype.card_fin] using h

theorem cut_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    ((run policy active origin q).2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + Fintype.card Agent * q := by
  have h := UpperRecordedGrid.cut_bound policy active origin (count (Agent := Agent) q) (schedule q)
  simpa only [run, count, Fintype.card_prod, Fintype.card_fin] using h

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hgood

theorem cuts_eq_common (q : ℕ) : cuts policy active origin q =
    UpperCommonGrid.cuts μ policy active (fun a => values origin (active a)) origin.cells q origin.history := by
  unfold cuts run UpperRecordedGrid.execute
  dsimp only
  rw [UpperRecordedGrid.samples_eq_mixture μ policy active origin hgood]
  rfl

include hpolicy hpositive

theorem run_wellFormed (q : ℕ) : WellFormed μ (run policy active origin q).2 :=
  UpperRecordedGrid.execute_wellFormed μ policy hpolicy active origin hgood hpositive _ _

theorem cuts_endpoints (q : ℕ) : cuts policy active origin q 0 = 0 ∧
    cuts policy active origin q (Fin.last (count (Agent := Agent) q + 1)) = 1 := by
  rw [cuts_eq_common μ policy active origin hgood]
  exact UpperCommonGrid.cuts_endpoints μ policy hpolicy active _ origin.cells
    hgood.1 hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive q origin.history

theorem logical_cells_small (q : ℕ) (a : Agent) (i : Fin (count (Agent := Agent) q + 1)) :
    (μ (active a)).real (logicalCells policy active origin q i) /
      (μ (active a)).real (domain origin.cells) ≤ 1 / (q + 1 : ℝ) := by
  unfold logicalCells
  rw [cuts_eq_common μ policy active origin hgood]
  exact UpperCommonGrid.logical_cells_small μ policy hpolicy active _ origin.cells
    hgood.1 hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive q origin.history a i

/-- Literal physical partition into `k*q+1` logical cell indices. Old joins
inside the buffer affect the physical representation but not this count. -/
theorem logical_partition (q : ℕ) :
    Pairwise (fun i j => Disjoint (logicalCells policy active origin q i) (logicalCells policy active origin q j)) ∧
    (∀ i, MeasurableSet (logicalCells policy active origin q i)) ∧
    (⋃ i, logicalCells policy active origin q i) = domain origin.cells := by
  unfold logicalCells
  rw [cuts_eq_common μ policy active origin hgood]
  exact UpperCommonGrid.logical_partition μ policy hpolicy active _ origin.cells
    hgood.1 hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive q origin.history

end Correctness

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem run_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q : ℕ) : Measurable (fun origin : State n => run policy active origin q) := by
  have hr : Measurable (fun p : State n × (Fin (Fintype.card (Agent × Fin q)) → Agent × I) =>
      UpperRecordedGrid.execute policy active p.1 (Fintype.card (Agent × Fin q)) p.2) :=
    UpperRecordedGrid.execute_measurable (n := n) (Agent := Agent) policy hpolicy active
      (Fintype.card (Agent × Fin q))
  have hin : Measurable (fun origin : State n =>
      (origin, (schedule (Agent := Agent) q : Fin (Fintype.card (Agent × Fin q)) → Agent × I))) :=
    measurable_id.prodMk measurable_const
  have hout := hr.comp hin
  exact hout

theorem cuts_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q : ℕ) : Measurable (fun origin => cuts policy active origin q) :=
  UpperCommonGrid.grid_measurable _ (fun i => (measurable_pi_apply i).comp
    (measurable_fst.comp (run_measurable policy hpolicy active q)))

end Measurability

end EnvyFreeResearch.Full.UpperRecordedQuantiles
