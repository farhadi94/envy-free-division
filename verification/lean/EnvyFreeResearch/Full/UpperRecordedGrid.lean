import EnvyFreeResearch.Full.UpperGridRecords

/-!
# A measure-independent recorded grid constructor

The program reads its cell masses and total masses from recorded Eval answers.
The measure profile occurs only in correctness and distribution theorems. Its
output records every endpoint and refines the physical domain without changing
any literal material; the logical grid remains a separate finite index set.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRecordedGrid

open UpperRecordedDomain UpperDomainDifference UpperCircularStage UpperStageMeasurable
  UpperDynamicExecutor UpperUnionSampling UpperCorrectionExecution UpperGridRecords
  UpperEndpointCache UpperMixtureSampling UpperAdaptiveProduct ProtocolMeasurable Chores

variable {n : ℕ} {Agent : Type*}

def step (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (history : History n) (draw : Agent × I) : ℝ × History n :=
  sampleExecution policy history (active draw.1) (values origin (active draw.1))
    (total origin (active draw.1)) origin.cells draw.2

def samples (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) : (Fin m → ℝ) × History n :=
  UpperFreshSamples.run (step policy active origin) m origin.history draw

def execute (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) : (Fin m → ℝ) × State n :=
  let result := samples policy active origin m draw
  (result.1, ⟨refineEndpoints origin.cells (List.ofFn result.1), result.2⟩)

theorem execute_domain (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) :
    domain (execute policy active origin m draw).2.cells = domain origin.cells :=
  refineEndpoints_domain _ _

theorem query_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) :
    (execute policy active origin m draw).2.history.length ≤ origin.history.length + m * (n + 1) := by
  apply UpperFreshSamples.cost_bound (step policy active origin) List.length (n + 1)
  intro h d
  exact (sampleExecution_query_bound policy h (active d.1) (values origin (active d.1))
    (total origin (active d.1)) origin.cells d.2).trans_eq (by omega)

theorem cut_bound (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) :
    ((execute policy active origin m draw).2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + m := by
  have h := UpperFreshSamples.cost_bound (step policy active origin)
    (fun h => (h.map Prod.fst).countP isCut) 1
    (fun h d => sampleExecution_cut_bound policy h (active d.1) (values origin (active d.1))
      (total origin (active d.1)) origin.cells d.2) m origin.history draw
  simpa only [execute, samples, mul_one] using h

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem samples_eq_mixture (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (m : ℕ) (draw : Fin m → Agent × I) :
    samples policy active origin m draw = UpperFreshSamples.run
      (UpperMixtureSampling.sample μ policy active (fun a => values origin (active a)) origin.cells)
      m origin.history draw := by
  have heq : step policy active origin =
      UpperMixtureSampling.sample μ policy active (fun a => values origin (active a)) origin.cells := by
    funext h d
    simp only [step, UpperMixtureSampling.sample, total_correct μ origin hgood]
  rw [samples, heq]

theorem samples_records (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (m : ℕ) (draw : Fin m → Agent × I) :
    let result := samples policy active origin m draw
    Truthful μ result.2 ∧ RecordedHistory origin.cells result.2 ∧ origin.history ⊆ result.2 ∧
      ∀ i, result.1 i ∈ Icc (0 : ℝ) 1 ∧ HasEndpoint result.2 (result.1 i) := by
  rw [samples_eq_mixture μ policy active origin hgood]
  exact mixture_run_records μ policy hpolicy active (fun a => values origin (active a)) origin.cells
    hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive m origin.history
    hgood.2.2.1 hgood.2.2.2 draw

/-- The grid's refined physical representation has a correct cache for every
original observer under every legal history-dependent reply policy. -/
theorem execute_wellFormed (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (m : ℕ) (draw : Fin m → Agent × I) :
    WellFormed μ (execute policy active origin m draw).2 := by
  have hr := samples_records μ policy hpolicy active origin hgood hpositive m draw
  apply refineEndpoints_wellFormed μ
    (⟨origin.cells, (samples policy active origin m draw).2⟩ : State n)
    ⟨hgood.1, hgood.2.1, hr.1, hr.2.1⟩
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact (hr.2.2.2 i).2

theorem execute_endpoints (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (m : ℕ) (draw : Fin m → Agent × I) (i : Fin m) :
    (execute policy active origin m draw).1 i ∈ Icc (0 : ℝ) 1 :=
  ((samples_records μ policy hpolicy active origin hgood hpositive m draw).2.2.2 i).1

variable [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [Nonempty Agent]

/-- Full iid mixture law for the measure-independent recorded program. -/
theorem iid_law (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Agent → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells)) (m : ℕ) :
    MeasurePreserving (fun draw => (execute policy active origin m draw).1)
      (tapeLaw (seedLaw Agent) m) (tapeLaw (mixture μ active origin.cells) m) := by
  have h := iid_sample_law μ policy hpolicy hmeas active (fun a => values origin (active a)) origin.cells
    hgood.1 hgood.2.1 (fun a => values_correct μ origin hgood (active a)) hpositive m origin.history
  convert h using 1
  funext draw
  exact congrArg Prod.fst (samples_eq_mixture μ policy active origin hgood m draw)

end Correctness

section Measurability

/-- Parameterized finite execution: the preparation data may itself be the
measurable result of preceding protocol stages. -/
theorem run_family_measurable {Parameter State Draw Sample : Type*}
    [MeasurableSpace Parameter] [MeasurableSpace State] [MeasurableSpace Draw] [MeasurableSpace Sample]
    (step : Parameter → State → Draw → Sample × State)
    (hstep : Measurable (fun p : Parameter × State × Draw => step p.1 p.2.1 p.2.2)) (m : ℕ) :
    Measurable (fun p : Parameter × State × (Fin m → Draw) => UpperFreshSamples.run (step p.1) m p.2.1 p.2.2) := by
  induction m with
  | zero => exact measurable_const.prodMk (measurable_fst.comp measurable_snd)
  | succ m ih =>
    let first (p : Parameter × State × (Fin (m + 1) → Draw)) := step p.1 p.2.1 (p.2.2 0)
    have hfirst : Measurable first := hstep.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))
    let rest (p : Parameter × State × (Fin (m + 1) → Draw)) :=
      UpperFreshSamples.run (step p.1) m (first p).2 (fun i => p.2.2 i.succ)
    have htail : Measurable (fun p : Parameter × State × (Fin (m + 1) → Draw) =>
        fun i : Fin m => p.2.2 i.succ) :=
      Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp (measurable_snd.comp measurable_snd))
    have hrest : Measurable rest := ih.comp (measurable_fst.prodMk ((measurable_snd.comp hfirst).prodMk htail))
    have hvalues : Measurable (fun p => Fin.cons (α := fun _ : Fin (m + 1) => Sample)
        (first p).1 (rest p).1) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst.comp hfirst
      · exact (measurable_pi_apply j).comp (measurable_fst.comp hrest)
    exact hvalues.prodMk (measurable_snd.comp hrest)

theorem ofFn_measurable {α : Type*} [MeasurableSpace α] (m : ℕ) :
    Measurable (List.ofFn : (Fin m → α) → List α) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · simpa only [listCode, Function.comp_def, List.length_ofFn] using
      (measurable_const : Measurable (fun _ : Fin m → α => m))
  · apply Measurable.of_eval
    intro k
    by_cases hk : k < m
    · simpa only [listCode, Function.comp_def, List.getElem?_ofFn, hk, dite_true] using
        measurable_some.comp (measurable_pi_apply (⟨k, hk⟩ : Fin m))
    · simpa only [listCode, Function.comp_def, List.getElem?_ofFn, hk, dite_false] using
        (measurable_const : Measurable (fun _ : Fin m → α => (none : Option α)))

variable [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem step_joint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy) (active : Agent → Fin n) :
    Measurable (fun p : State n × History n × (Agent × I) => step policy active p.1 p.2.1 p.2.2) := by
  have hcutter : Measurable (fun p : State n × History n × (Agent × I) => active p.2.2.1) :=
    (measurable_of_countable active).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact sampleExecution_joint_measurable policy hpolicy _ _ _ _ _ _
    (measurable_fst.comp measurable_snd) hcutter
    (values_measurable _ _ measurable_fst hcutter)
    (total_measurable _ _ measurable_fst hcutter)
    (state_cells_measurable.comp measurable_fst)
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem samples_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (m : ℕ) :
    Measurable (fun p : State n × (Fin m → Agent × I) => samples policy active p.1 m p.2) := by
  have hr : Measurable (fun p : State n × History n × (Fin m → Agent × I) =>
      UpperFreshSamples.run (step policy active p.1) m p.2.1 p.2.2) :=
    run_family_measurable (Parameter := State n) (State := History n)
      (Draw := Agent × I) (Sample := ℝ) (step policy active)
      (step_joint_measurable policy hpolicy active) m
  have hin : Measurable (fun p : State n × (Fin m → Agent × I) => (p.1, p.1.history, p.2)) :=
    measurable_fst.prodMk ((state_history_measurable.comp measurable_fst).prodMk measurable_snd)
  have hout := hr.comp hin
  change Measurable (fun p : State n × (Fin m → Agent × I) =>
    UpperFreshSamples.run (step policy active p.1) m p.1.history p.2)
  exact hout

/-- The whole physical grid constructor is jointly measurable in the
preceding recorded state and its fresh sample tape. -/
theorem execute_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (m : ℕ) :
    Measurable (fun p : State n × (Fin m → Agent × I) => execute policy active p.1 m p.2) := by
  have hr := samples_measurable policy hpolicy active m
  apply (measurable_fst.comp hr).prodMk
  apply measurable_comap_iff.mpr
  change Measurable (fun p : State n × (Fin m → Agent × I) =>
    (refineEndpoints p.1.cells (List.ofFn (samples policy active p.1 m p.2).1),
      (samples policy active p.1 m p.2).2))
  exact (refineEndpoints_measurable _ _ (state_cells_measurable.comp measurable_fst)
    ((ofFn_measurable m).comp (measurable_fst.comp hr))).prodMk (measurable_snd.comp hr)

end Measurability

end EnvyFreeResearch.Full.UpperRecordedGrid
