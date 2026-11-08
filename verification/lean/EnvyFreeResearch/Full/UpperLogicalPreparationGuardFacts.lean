import EnvyFreeResearch.Full.UpperLogicalPreparationGuardState

/-! Passing the computed preparation guard supplies the concrete physical
and cached facts consumed by correction setup. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparationGuard

open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRecordedQuantiles UpperDomainDifference UpperGridCells UpperLogicalCells Chores
  UpperWitnessExtraction UpperRepresentativeSupply

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

theorem selectedParents_eq (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent))
    (pairs : List (Fin (count (Agent := Agent) q + m + 1) × Fin (count (Agent := Agent) q + m + 1)))
    (final : Finset (Fin (count (Agent := Agent) q + 1)))
    (hexec : representativeRun policy active origin q m draw jobs = some (pairs, final)) :
    selectedParents policy active origin q m draw jobs = final := by
  simp only [selectedParents, hexec]

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

/-- The actual deterministic selector's parent count follows from its proved
completion, independently of all later parent labels. -/
theorem selectedParents_card (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent))
    (hbudget : 2 * jobs.length < q + 1) :
    (selectedParents policy active origin q m draw jobs).card ≤ 2 * jobs.length := by
  have hb : (((∅ : Finset (Fin (count (Agent := Agent) q + 1))).card + 2 * jobs.length : ℕ) : ℝ) *
      (1 / (q + 1 : ℝ)) < 1 := by
    simp only [Finset.card_empty, zero_add, mul_one_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < q + 1)).mpr
    exact_mod_cast hbudget
  obtain ⟨pairs, final, hexec, _, _, hcard⟩ := recorded_run_completes μ policy hpolicy active origin hgood hpositive
    q m draw jobs ∅ hb
  rw [selectedParents_eq policy active origin q m draw jobs pairs final hexec]
  simpa only [Finset.card_empty, zero_add] using hcard

theorem passing_lower_mass (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m jobs theta cap draw labels = true) (a : Agent) :
    (theta : ℝ) / 2 * (μ (active a)).real (domain origin.cells) ≤
      (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells) := by
  have h := ((guard_eq_true policy active origin q m jobs theta cap draw labels).mp hpass).1 a
  rw [total_correct μ origin hgood,
    total_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)] at h
  exact h

theorem passing_positive (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m jobs theta cap draw labels = true) (a : Agent) :
    0 < (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells) :=
  (mul_pos (div_pos htheta (by norm_num)) (hpositive a)).trans_le
    (passing_lower_mass μ policy hpolicy active origin hgood hpositive q m jobs theta cap draw labels hpass a)

theorem passing_table_small (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m jobs theta cap draw labels = true) (a : Agent)
    (e : Fin (count (Agent := Agent) q + m + 1)) :
    cachedMass (reserveState policy active origin q m draw theta labels)
        (UpperGridMerge.cuts policy active origin q m draw) (active a) e /
      total (reserveState policy active origin q m draw theta labels) (active a) ≤
        2 / ((theta : ℝ) * (q + 1 : ℝ)) :=
  reserveState_table_small μ policy hpolicy active origin hgood hpositive q m draw theta htheta labels
    (passing_lower_mass μ policy hpolicy active origin hgood hpositive q m jobs theta cap draw labels hpass) a e

/-- The passed parent test applies to every witness extracted from the actual
returned list, even when its row normalizer depends on the reserve labels. -/
theorem passing_witness_disjoint {Index : Type*} [Fintype Index]
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : Index → Agent × Agent) (normalizer : Agent → ℝ)
    (theta : I) (cap : ℝ) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m (roundJobs jobs) theta cap draw labels = true)
    (pairs : List (Fin (count (Agent := Agent) q + m + 1) × Fin (count (Agent := Agent) q + m + 1)))
    (final : Finset (Fin (count (Agent := Agent) q + 1)))
    (hexec : representativeRun policy active origin q m draw (roundJobs jobs) = some (pairs, final))
    (hlength : pairs.length = Fintype.card Index) (i : Index) :
    Disjoint (UpperGridMerge.logicalCells policy active origin q m draw
      (picked (UpperGridCache.table policy active origin q m draw) normalizer jobs pairs 0 i))
      (domain (reserveState policy active origin q m draw theta labels).cells) := by
  rw [reserveState_domain μ policy hpolicy active origin hgood hpositive q m draw theta labels]
  have hparents := ((guard_eq_true policy active origin q m (roundJobs jobs) theta cap draw labels).mp hpass).2.2
  rw [selectedParents_eq policy active origin q m draw (roundJobs jobs) pairs final hexec] at hparents
  exact picked_disjoint_reserve _ (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    normalizer _ _ _ _
    (UpperRecordedParents.cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw)
    (UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q).1
    jobs ∅ pairs final hexec hlength 0 theta labels hparents i

end Correctness

/-- A single bundle of concrete passing facts for the final full-history
reserve. The construction and frozen-domain identity are proved upstream. -/
structure PassingFacts (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) (cap : ℝ) : Prop where
  wellFormed : WellFormed μ (reserveState policy active origin q m draw theta labels)
  history : (reserveState policy active origin q m draw theta labels).history =
    (UpperGridCache.aligned policy active origin q m draw).history
  fixed_domain : domain (reserveState policy active origin q m draw theta labels).cells =
    domain (frozenReserveState policy active origin q theta labels).cells
  subset : domain (reserveState policy active origin q m draw theta labels).cells ⊆ domain origin.cells
  separated : ∀ e, SeparatedAt (UpperGridMerge.cuts policy active origin q m draw e)
    (reserveState policy active origin q m draw theta labels).cells
  lower_mass : ∀ a, (theta : ℝ) / 2 * (μ (active a)).real (domain origin.cells) ≤
    (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells)
  positive : ∀ a, 0 < (μ (active a)).real (domain (reserveState policy active origin q m draw theta labels).cells)
  table_small : ∀ a e, cachedMass (reserveState policy active origin q m draw theta labels)
      (UpperGridMerge.cuts policy active origin q m draw) (active a) e /
      total (reserveState policy active origin q m draw theta labels) (active a) ≤ 2 / ((theta : ℝ) * (q + 1 : ℝ))
  count_le : ((reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels).card : ℝ) ≤ cap
  empty_outside : ∀ e, e ∉ reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels →
    cell (domain (reserveState policy active origin q m draw theta labels).cells)
      (UpperGridMerge.cuts policy active origin q m draw) e = ∅

theorem passing_facts (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I)
    (hpass : guard policy active origin q m jobs theta cap draw labels = true) :
    PassingFacts μ policy active origin q m draw theta labels cap := by
  exact ⟨reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels,
    reserveState_history policy active origin q m draw theta labels,
    final_reserve_eq_frozen μ policy hpolicy active origin hgood hpositive q m draw theta labels,
    reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw theta labels,
    reserveState_separated policy active origin q m draw theta labels,
    passing_lower_mass μ policy hpolicy active origin hgood hpositive q m jobs theta cap draw labels hpass,
    passing_positive μ policy hpolicy active origin hgood hpositive q m jobs theta htheta cap draw labels hpass,
    passing_table_small μ policy hpolicy active origin hgood hpositive q m jobs theta htheta cap draw labels hpass,
    ((guard_eq_true policy active origin q m jobs theta cap draw labels).mp hpass).2.1,
    reserveState_cell_empty μ policy hpolicy active origin hgood hpositive q m draw theta labels⟩

end EnvyFreeResearch.Full.UpperLogicalPreparationGuard
