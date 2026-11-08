import EnvyFreeResearch.Full.UpperLogicalPreparationGuardFacts

/-!
# Preparation rejection on the original fine-tape × independent-label law

Each fibre over the complete fine sampler tape has the three proved label
bounds. Tonelli averages these fibres on the original product space. No
sample law is conditioned on preparation success or reconstructed from points.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparationGuard

open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRecordedQuantiles UpperMixtureSampling UpperAdaptiveProduct Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

/-- The three explicit preparation failure budgets. -/
def failureBudget (q m rounds : ℕ) (theta : I) (cap : ℝ) : ℝ :=
  4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ)) +
    2 * (theta : ℝ) * m / cap + 2 * rounds * (theta : ℝ)

section Fibre

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

/-- Fixed-fine-tape estimate. The actual selected-parent set is fixed before
the independent labels, whereas witnesses may use label-dependent normalizers. -/
theorem failure_fiber_probability (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent))
    (hbudget : 2 * jobs.length < q + 1) (hgrid : count (Agent := Agent) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    UpperReserve.labelLaw {labels | guard policy active origin q m jobs theta cap draw labels = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) := by
  let badMass : Set (Fin (count (Agent := Agent) q + 1) → I) :=
    {labels | ∃ a, total (reserveState policy active origin q m draw theta labels) (active a) <
      (theta : ℝ) / 2 * total origin (active a)}
  let badCount : Set (Fin (count (Agent := Agent) q + 1) → I) :=
    {labels | cap < ((reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels).card : ℝ)}
  let badParent : Set (Fin (count (Agent := Agent) q + 1) → I) :=
    {labels | ∃ p ∈ selectedParents policy active origin q m draw jobs, labels p ≤ theta}
  have hmass : UpperReserve.labelLaw badMass ≤
      ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ))) := by
    apply (measure_mono (show badMass ⊆ {labels | ∃ a,
      total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a) < (theta : ℝ) / 2 ∨
      3 * (theta : ℝ) / 2 < total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a)} from ?_)).trans
      (reserveState_mass_probability μ policy hpolicy active origin hgood hpositive q m draw theta htheta)
    rintro labels ⟨a, ha⟩
    refine ⟨a, Or.inl ?_⟩
    apply (div_lt_iff₀ (show 0 < total origin (active a) by rw [total_correct μ origin hgood]; exact hpositive a)).mpr
    exact ha
  have hcount : UpperReserve.labelLaw badCount ≤ ENNReal.ofReal (2 * (theta : ℝ) * m / cap) :=
    recorded_reserve_count_probability policy active origin q m draw theta cap hcap hgrid
  have hparent : UpperReserve.labelLaw badParent ≤ ENNReal.ofReal (2 * jobs.length * (theta : ℝ)) :=
    selected_parent_failure _ theta jobs.length
      (selectedParents_card μ policy hpolicy active origin hgood hpositive q m draw jobs hbudget)
  have hsub : {labels | guard policy active origin q m jobs theta cap draw labels = false} ⊆
      (badMass ∪ badCount) ∪ badParent := by
    intro labels hfalse
    have hn : ¬Passes policy active origin q m jobs theta cap draw labels := by
      intro hp
      have ht := (guard_eq_true policy active origin q m jobs theta cap draw labels).mpr hp
      exact Bool.false_ne_true (hfalse.symm.trans ht)
    rcases not_and_or.mp hn with hlower | hrest
    · obtain ⟨a, ha⟩ := not_forall.mp hlower
      exact Or.inl (Or.inl ⟨a, lt_of_not_ge ha⟩)
    · rcases not_and_or.mp hrest with hc | hp
      · exact Or.inl (Or.inr (lt_of_not_ge hc))
      · push Not at hp
        exact Or.inr hp
  calc
    _ ≤ UpperReserve.labelLaw ((badMass ∪ badCount) ∪ badParent) := measure_mono hsub
    _ ≤ UpperReserve.labelLaw (badMass ∪ badCount) + UpperReserve.labelLaw badParent := measure_union_le _ _
    _ ≤ (UpperReserve.labelLaw badMass + UpperReserve.labelLaw badCount) + UpperReserve.labelLaw badParent :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ))) +
        ENNReal.ofReal (2 * (theta : ℝ) * m / cap)) + ENNReal.ofReal (2 * jobs.length * (theta : ℝ)) :=
      add_le_add (add_le_add hmass hcount) hparent
    _ = _ := by
      unfold failureBudget
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]

end Fibre

section Product

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

/-- Tonelli on the original product law, using the derived fibre estimate.
This works for any probability law of the complete fine tape. -/
theorem failure_product_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (hbudget : 2 * jobs.length < q + 1)
    (hgrid : count (Agent := Agent) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap)
    (fineLaw : Measure (Fin m → Agent × I)) [IsProbabilityMeasure fineLaw] :
    (fineLaw.prod UpperReserve.labelLaw) {p | guard policy active origin q m jobs theta cap p.1 p.2 = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) := by
  have hm : MeasurableSet {p : (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I) |
      guard policy active origin q m jobs theta cap p.1 p.2 = false} :=
    measurableSet_eq_fun (guard_measurable policy hmeas active origin q m jobs theta cap) measurable_const
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _draw, ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) ∂fineLaw := by
      apply lintegral_mono
      intro draw
      exact failure_fiber_probability μ policy hpolicy active origin hgood hpositive q m draw jobs hbudget hgrid theta htheta cap hcap
    _ = _ := by simp

/-- The actual original fine sampler tape and fresh independent parent labels. -/
def originalLaw (q m : ℕ) : Measure ((Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I)) :=
  (tapeLaw (seedLaw Agent) m).prod UpperReserve.labelLaw

instance originalLaw_probability (q m : ℕ) : IsProbabilityMeasure (originalLaw (Agent := Agent) q m) := by
  unfold originalLaw
  infer_instance

theorem original_tape_failure_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (hbudget : 2 * jobs.length < q + 1)
    (hgrid : count (Agent := Agent) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    originalLaw q m {p | guard policy active origin q m jobs theta cap p.1 p.2 = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) :=
  failure_product_probability μ policy hpolicy hmeas active origin hgood hpositive q m jobs hbudget hgrid theta htheta cap hcap _

/-- The point projection has its iid law on the full original preparation
parameter. This law is never conditioned on passing the Boolean guard. -/
theorem original_samples_law (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells)) (q m : ℕ) :
    MeasurePreserving (fun p => (UpperGridMerge.prepare policy active origin q m p.1).2.1)
      (originalLaw (Agent := Agent) q m) (tapeLaw (mixture μ active origin.cells) m) :=
  (UpperGridMerge.iid_sample_law μ policy hpolicy hmeas active origin hgood hpositive q m).comp measurePreserving_fst

end Product

end EnvyFreeResearch.Full.UpperLogicalPreparationGuard
