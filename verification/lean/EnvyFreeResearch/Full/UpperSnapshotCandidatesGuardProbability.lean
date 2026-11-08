import EnvyFreeResearch.Full.UpperSnapshotCandidatesGuard

/-! The stronger Snapshot guard uses the same two-sided reserve mass event
and the same three-term preparation budget, on the original product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperMixtureSampling UpperAdaptiveProduct Chores
variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

section Fibre
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

/-- Both reserve tails share this single existing exception bound. The
upper-tail check adds no term to the manuscript preparation budget. -/
theorem snapshotGuard_fiber_probability (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent))
    (hbudget : 2 * jobs.length < q + 1) (hgrid : count (Agent := Agent) q + 1 ≤ m)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    UpperReserve.labelLaw {labels | snapshotGuard policy active origin q m jobs theta cap draw labels = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) := by
  let badMass : Set (Fin (count (Agent := Agent) q + 1) → I) := {labels | ∃ a,
    total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a) < (theta : ℝ) / 2 ∨
    3 * (theta : ℝ) / 2 < total (reserveState policy active origin q m draw theta labels) (active a) / total origin (active a)}
  let badCount : Set (Fin (count (Agent := Agent) q + 1) → I) :=
    {labels | cap < ((reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels).card : ℝ)}
  let badParent : Set (Fin (count (Agent := Agent) q + 1) → I) :=
    {labels | ∃ p ∈ selectedParents policy active origin q m draw jobs, labels p ≤ theta}
  have hmass : UpperReserve.labelLaw badMass ≤
      ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ))) :=
    reserveState_mass_probability μ policy hpolicy active origin hgood hpositive q m draw theta htheta
  have hcount : UpperReserve.labelLaw badCount ≤ ENNReal.ofReal (2 * (theta : ℝ) * m / cap) :=
    recorded_reserve_count_probability policy active origin q m draw theta cap hcap hgrid
  have hparent : UpperReserve.labelLaw badParent ≤ ENNReal.ofReal (2 * jobs.length * (theta : ℝ)) :=
    selected_parent_failure _ theta jobs.length
      (selectedParents_card μ policy hpolicy active origin hgood hpositive q m draw jobs hbudget)
  have htotal (a : Agent) : 0 < total origin (active a) := by
    rw [total_correct μ origin hgood]
    exact hpositive a
  have hsub : {labels | snapshotGuard policy active origin q m jobs theta cap draw labels = false} ⊆
      (badMass ∪ badCount) ∪ badParent := by
    intro labels hfalse
    rcases (snapshotGuard_false policy active origin q m jobs theta cap draw labels).mp hfalse with hlower | hupper
    · have hn : ¬Passes policy active origin q m jobs theta cap draw labels := by
        intro hp
        have ht := (guard_eq_true policy active origin q m jobs theta cap draw labels).mpr hp
        exact Bool.false_ne_true (hlower.symm.trans ht)
      rcases not_and_or.mp hn with hlower | hrest
      · obtain ⟨a, ha⟩ := not_forall.mp hlower
        exact Or.inl (Or.inl ⟨a, Or.inl ((div_lt_iff₀ (htotal a)).mpr (lt_of_not_ge ha))⟩)
      · rcases not_and_or.mp hrest with hc | hp
        · exact Or.inl (Or.inr (lt_of_not_ge hc))
        · push Not at hp
          exact Or.inr hp
    · have hn : ¬∀ a, total (reserveState policy active origin q m draw theta labels) (active a) ≤
          3 * (theta : ℝ) / 2 * total origin (active a) := by
        intro hu
        have ht := (upperReserve_eq_true _ _ _ _).mpr hu
        exact Bool.false_ne_true (hupper.symm.trans ht)
      obtain ⟨a, ha⟩ := not_forall.mp hn
      exact Or.inl (Or.inl ⟨a, Or.inr ((lt_div_iff₀ (htotal a)).mpr (lt_of_not_ge ha))⟩)
  calc
    _ ≤ UpperReserve.labelLaw ((badMass ∪ badCount) ∪ badParent) := measure_mono hsub
    _ ≤ (UpperReserve.labelLaw badMass + UpperReserve.labelLaw badCount) + UpperReserve.labelLaw badParent :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (4 * Fintype.card Agent / ((theta : ℝ) * (q + 1 : ℝ))) +
        ENNReal.ofReal (2 * (theta : ℝ) * m / cap)) + ENNReal.ofReal (2 * jobs.length * (theta : ℝ)) :=
      add_le_add (add_le_add hmass hcount) hparent
    _ = _ := by
      unfold failureBudget
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
end Fibre

section Product
variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem snapshotGuard_product_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (hbudget : 2 * jobs.length < q + 1)
    (hgrid : count (Agent := Agent) q + 1 ≤ m) (theta : I) (htheta : 0 < (theta : ℝ))
    (cap : ℝ) (hcap : 0 < cap) (fineLaw : Measure (Fin m → Agent × I)) [IsProbabilityMeasure fineLaw] :
    (fineLaw.prod UpperReserve.labelLaw) {p | snapshotGuard policy active origin q m jobs theta cap p.1 p.2 = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) := by
  have hm : MeasurableSet {p : (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I) |
      snapshotGuard policy active origin q m jobs theta cap p.1 p.2 = false} :=
    measurableSet_eq_fun (snapshotGuard_measurable policy hmeas active origin q m jobs theta cap) measurable_const
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _draw, ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) ∂fineLaw := by
      apply lintegral_mono
      intro draw
      exact snapshotGuard_fiber_probability μ policy hpolicy active origin hgood hpositive q m draw jobs hbudget hgrid theta htheta cap hcap
    _ = _ := by simp

theorem snapshotGuard_original_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (hbudget : 2 * jobs.length < q + 1)
    (hgrid : count (Agent := Agent) q + 1 ≤ m) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (hcap : 0 < cap) :
    originalLaw q m {p | snapshotGuard policy active origin q m jobs theta cap p.1 p.2 = false} ≤
      ENNReal.ofReal (failureBudget (Agent := Agent) q m jobs.length theta cap) :=
  snapshotGuard_product_probability μ policy hpolicy hmeas active origin hgood hpositive q m jobs
    hbudget hgrid theta htheta cap hcap _
end Product

/-- A pathwise rejection decomposition may use the stronger guard in place
of the old one. This is the precise shared-charge union step for Repair. -/
theorem strengthened_trial_union {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (rejected cycle correction : Set Ω) (guard upper : Ω → Bool) (preparationBound cycleBound correctionBound : ℝ≥0∞)
    (hsub : rejected ⊆ ({x | guard x = false} ∪ cycle) ∪ correction)
    (hpreparation : Q {x | (guard x && upper x) = false} ≤ preparationBound)
    (hcycle : Q cycle ≤ cycleBound) (hcorrection : Q correction ≤ correctionBound) :
    Q (rejected ∪ {x | upper x = false}) ≤ preparationBound + cycleBound + correctionBound := by
  have hs : rejected ∪ {x | upper x = false} ⊆ ({x | (guard x && upper x) = false} ∪ cycle) ∪ correction := by
    intro x hx
    rcases hx with hr | hu
    · rcases hsub hr with (hg | hc) | hc
      · exact Or.inl (Or.inl (Bool.and_eq_false_iff.mpr (Or.inl hg)))
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hc
    · exact Or.inl (Or.inl (Bool.and_eq_false_iff.mpr (Or.inr hu)))
  exact (measure_mono hs).trans (((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl)).trans (add_le_add (add_le_add hpreparation hcycle) hcorrection))

end EnvyFreeResearch.Full.UpperSnapshotCandidates
