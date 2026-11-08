import EnvyFreeResearch.Full.UpperQuantileBounds

/-!
# Actual ordinary-query quantile execution

A fixed finite schedule asks each active agent for its interior quantiles
on the recorded buffer. The actual returned endpoints, including arbitrary
legal plateau roots and full preceding histories, have the prescribed
normalized cumulative values. Every call and endpoint recording is counted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval BigOperators Classical

namespace EnvyFreeResearch.Full.UpperQuantileExecution

open UpperFreshSamples UpperCircularStage UpperRecordedDomain UpperUnionSampling
  UpperMixtureSampling UpperUnionMeasurable UpperStageMeasurable Chores

theorem run_output_spec {State Draw Output : Type*} (step : State → Draw → Output × State)
    (P : Draw → Output → Prop) (hstep : ∀ state draw, P draw (step state draw).1)
    (m : ℕ) (state : State) (draw : Fin m → Draw) :
    ∀ i, P (draw i) ((UpperFreshSamples.run step m state draw).1 i) := by
  induction m generalizing state with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hstep state (draw 0)
    · exact ih (step state (draw 0)).2 (fun i => draw i.succ) j

def target {q : ℕ} (j : Fin q) : I :=
  ⟨((j.val : ℝ) + 1) / (q + 1), by positivity,
    (div_le_one (by positivity : (0 : ℝ) < q + 1)).mpr (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt j.isLt) 1)⟩

theorem target_positive {q : ℕ} (j : Fin q) : 0 < (target j : ℝ) := by
  dsimp [target]
  positivity

variable {Agent : Type*} [Fintype Agent]

def schedule (q : ℕ) (i : Fin (Fintype.card (Agent × Fin q))) : Agent × I :=
  let job := (Fintype.equivFin (Agent × Fin q)).symm i
  (job.1, target job.2)

def jobIndex {q : ℕ} (a : Agent) (j : Fin q) : Fin (Fintype.card (Agent × Fin q)) :=
  Fintype.equivFin (Agent × Fin q) (a, j)

theorem schedule_job {q : ℕ} (a : Agent) (j : Fin q) : schedule q (jobIndex a j) = (a, target j) := by
  simp only [schedule, jobIndex, Equiv.symm_apply_apply]

def execution {n : ℕ} (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) (history : History n) :
    (Fin (Fintype.card (Agent × Fin q)) → ℝ) × History n :=
  UpperFreshSamples.run (sample μ policy active cached cells) _ history (schedule q)

def root {n : ℕ} (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ)
    (history : History n) (a : Agent) (j : Fin q) : ℝ :=
  (execution μ policy active cached cells q history).1 (jobIndex a j)

/-- Quantile correctness is proved from the actual scheduled Cut executor,
not an independently supplied family of roots. -/
theorem roots_spec {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (cached : Agent → Component → ℝ) (cells : List Component)
    (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
    (hcache : ∀ a c, c ∈ cells → cached a c = mass (μ (active a)) c)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells))
    (q : ℕ) (history : History n) (a : Agent) (j : Fin q) :
    root μ policy active cached cells q history a j ∈ Icc (0 : ℝ) 1 ∧
      cdf (cond (μ (active a)) (domain cells)) (root μ policy active cached cells q history a j) =
        ((j.val : ℝ) + 1) / (q + 1) := by
  let P (draw : Agent × I) (endpoint : ℝ) : Prop :=
    0 < (draw.2 : ℝ) → endpoint ∈ Icc (0 : ℝ) 1 ∧
      cdf (cond (μ (active draw.1)) (domain cells)) endpoint = (draw.2 : ℝ)
  have hstep (h : History n) (draw : Agent × I) : P draw (sample μ policy active cached cells h draw).1 := by
    intro hdraw
    have hs := sampleExecution_spec μ policy hpolicy h (active draw.1) (cached draw.1) cells
      hordered hdisjoint (hcache draw.1) (hpositive draw.1) draw.2 hdraw
    exact ⟨hs.1, hs.2.1⟩
  have h := run_output_spec (sample μ policy active cached cells) P hstep
    (Fintype.card (Agent × Fin q)) history (schedule q) (jobIndex a j)
  rw [schedule_job] at h
  exact h (target_positive j)

theorem query_bound {n : ℕ} (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) (history : History n) :
    (execution μ policy active cached cells q history).2.length ≤
      history.length + (Fintype.card Agent * q) * (n + 1) := by
  simpa only [execution, Fintype.card_prod, Fintype.card_fin] using
    samples_query_bound μ policy active cached cells (Fintype.card (Agent × Fin q)) history (schedule q)

theorem cut_bound {n : ℕ} (μ : Fin n → Measure ℝ) (policy : Policy n) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) (history : History n) :
    ((execution μ policy active cached cells q history).2.map Prod.fst).countP isCut ≤
      (history.map Prod.fst).countP isCut + Fintype.card Agent * q := by
  simpa only [execution, Fintype.card_prod, Fintype.card_fin] using
    samples_cut_bound μ policy active cached cells (Fintype.card (Agent × Fin q)) history (schedule q)

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem execution_measurable {n : ℕ} (μ : Fin n → Measure ℝ) (policy : Policy n)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n)
    (cached : Agent → Component → ℝ) (cells : List Component) (q : ℕ) :
    Measurable (execution μ policy active cached cells q) :=
  (run_measurable (sample μ policy active cached cells)
    (sample_measurable μ policy hmeas active cached cells) _).comp
      (measurable_id.prodMk measurable_const)

end Measurability

end EnvyFreeResearch.Full.UpperQuantileExecution
