import EnvyFreeResearch.Full.UpperRecordedGrid
import EnvyFreeResearch.Full.UpperQuantileExecution
import EnvyFreeResearch.Full.UpperSignedCircular
import EnvyFreeResearch.Full.UpperGridCells

/-! A genuine sequential shared-circle endpoint executor. It uses the
existing ordinary union-Cut program, retains every observer recording, and
refines the literal domain only at actual returned endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperCircular UpperPhysical UpperGridRecords UpperDomainDifference UpperUnionSampling Chores
abbrev Circle := UpperCircular.Circle
variable {n J : ℕ}

def endpointTape (shifts : Fin J → Circle) (start : Circle) : Fin J → Unit × I :=
  fun j => ((), value (start + shifts j))

/-- One shared uniform start drives all cumulative boundary queries. There
is no iid-endpoint assumption, and each later query sees the full history. -/
def execute (policy : Policy n) (origin : State n) (cutter : Fin n)
    (shifts : Fin J → Circle) (start : Circle) : (Fin J → ℝ) × State n :=
  UpperRecordedGrid.execute policy (fun _ : Unit => cutter) origin J (endpointTape shifts start)

theorem execute_domain (policy : Policy n) (origin : State n) (cutter : Fin n)
    (shifts : Fin J → Circle) (start : Circle) :
    domain (execute policy origin cutter shifts start).2.cells = domain origin.cells :=
  UpperRecordedGrid.execute_domain _ _ _ _ _

theorem execute_query_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (shifts : Fin J → Circle) (start : Circle) :
    (execute policy origin cutter shifts start).2.history.length ≤ origin.history.length + J * (n + 1) :=
  UpperRecordedGrid.query_bound _ _ _ _ _

theorem execute_cut_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (shifts : Fin J → Circle) (start : Circle) :
    ((execute policy origin cutter shifts start).2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + J := UpperRecordedGrid.cut_bound _ _ _ _ _

variable {X : Type*} [MeasurableSpace X]

theorem endpointTape_measurable (shifts : X → Fin J → Circle) (start : X → Circle)
    (hshifts : ∀ j, Measurable (fun x => shifts x j)) (hstart : Measurable start) :
    Measurable (fun x => endpointTape (shifts x) (start x)) :=
  Measurable.of_eval (fun j => measurable_const.prodMk (measurable_value.comp (hstart.add (hshifts j))))

theorem execute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (origin : X → State n) (cutter : Fin n) (shifts : X → Fin J → Circle) (start : X → Circle)
    (horigin : Measurable origin) (hshifts : ∀ j, Measurable (fun x => shifts x j)) (hstart : Measurable start) :
    Measurable (fun x => execute policy (origin x) cutter (shifts x) (start x)) := by
  have hr : Measurable (fun p : State n × (Fin J → Unit × I) =>
      UpperRecordedGrid.execute policy (fun _ : Unit => cutter) p.1 J p.2) :=
    UpperRecordedGrid.execute_measurable policy hmeas (fun _ : Unit => cutter) J
  have hi : Measurable (fun x => (origin x, endpointTape (shifts x) (start x))) :=
    horigin.prodMk (endpointTape_measurable shifts start hshifts hstart)
  convert hr.comp hi using 1
  rfl

section Correctness
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
include hpolicy hgood hpositive

theorem execute_wellFormed (shifts : Fin J → Circle) (start : Circle) :
    WellFormed μ (execute policy origin cutter shifts start).2 :=
  UpperRecordedGrid.execute_wellFormed μ policy hpolicy (fun _ : Unit => cutter) origin hgood (fun _ => hpositive) _ _

theorem execute_records (shifts : Fin J → Circle) (start : Circle) :
    origin.history ⊆ (execute policy origin cutter shifts start).2.history ∧
      ∀ j, (execute policy origin cutter shifts start).1 j ∈ Icc (0 : ℝ) 1 ∧
        HasEndpoint (execute policy origin cutter shifts start).2.history ((execute policy origin cutter shifts start).1 j) := by
  exact (UpperRecordedGrid.samples_records μ policy hpolicy (fun _ : Unit => cutter) origin hgood
    (fun _ => hpositive) J (endpointTape shifts start)).2.2

/-- Actual endpoint CDF identities hold at every shared start, despite each
root being chosen after all earlier endpoints and their recorded answers. -/
theorem endpoint_cdf (shifts : Fin J → Circle) (start : Circle) (j : Fin J) :
    cdf (cond (μ cutter) (domain origin.cells)) ((execute policy origin cutter shifts start).1 j) =
      (value (start + shifts j) : ℝ) := by
  let P (draw : Unit × I) (endpoint : ℝ) : Prop :=
    0 < (draw.2 : ℝ) → cdf (cond (μ cutter) (domain origin.cells)) endpoint = (draw.2 : ℝ)
  have hstep (history : History n) (draw : Unit × I) :
      P draw (UpperRecordedGrid.step policy (fun _ : Unit => cutter) origin history draw).1 := by
    intro hdraw
    unfold UpperRecordedGrid.step
    rw [total_correct μ origin hgood cutter]
    exact (sampleExecution_spec μ policy hpolicy history cutter (values origin cutter) origin.cells
      hgood.1 hgood.2.1 (values_correct μ origin hgood cutter) hpositive draw.2 hdraw).2.1
  have h := UpperQuantileExecution.run_output_spec (UpperRecordedGrid.step policy (fun _ : Unit => cutter) origin)
    P hstep J origin.history (endpointTape shifts start) j
  exact h (value_positive _)

/-- Each boundary has the normalized cutter marginal before its group's
shared start. The endpoints are not asserted mutually independent. -/
theorem endpoint_law (hmeas : MeasurablePolicy policy) (shifts : Fin J → Circle) (j : Fin J) :
    HasLaw (fun start => (execute policy origin cutter shifts start).1 j)
      (cond (μ cutter) (domain origin.cells)) (volume : Measure Circle) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain origin.cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  apply circular_endpoint_law _ (shifts j) _
    ((measurable_pi_apply j).comp (measurable_fst.comp
      (execute_measurable policy hmeas (fun _ => origin) cutter (fun _ => shifts) id
        measurable_const (fun _ => measurable_const) measurable_id)))
  exact ae_of_all _ (fun start => endpoint_cdf μ policy hpolicy origin hgood cutter hpositive shifts start j)

end Correctness
end EnvyFreeResearch.Full.UpperSnapshotSmall
