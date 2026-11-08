import EnvyFreeResearch.Full.UpperRepairTrialProgram

/-! The actual successful preparation branch supplies every elementary
physical/cache/target hypothesis of the correction probability theorem. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperRepairPreparationChecks

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairJobs UpperLogicalPreparation UpperPreparedTrialProgram
  UpperIdealPayments UpperPreparedEnvelopeMean UpperRepairTrialProgram

variable {n k : ℕ} [Nonempty (Fin k)]

def Near (chores : Bool) (μ : Fin n → Measure ℝ) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (tau : ℝ) : Prop :=
  ∀ i j, (if chores then
    (μ (active i)).real (domain (old i).cells) - (μ (active i)).real (domain (old j).cells)
  else (μ (active i)).real (domain (old j).cells) - (μ (active i)).real (domain (old i).cells)) ≤
      tau * (μ (active i)).real (domain origin.cells)

theorem targets_execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L) (lam : ℝ) :
    dataTargets hk q chores active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold lam =
      if chores then choreTargets (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
        (disagreement policy active origin q m draw theta labels) lam (cellCap q theta)
      else cakeTargets (cachedMatrix hk policy active origin old q m L draw theta labels pi threshold)
        (disagreement policy active origin q m draw theta labels) lam := by
  unfold dataTargets
  rw [dataMatrix_execute, dataDisagreement_execute]

section Actual

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem actual_targets (hk : 2 ≤ k) (chores : Bool) (old : Fin k → State n)
    (hold : ∀ j, WellFormed μ (old j)) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap : ℝ) (labels : Labels k q)
    (hpass : UpperLogicalPreparationGuard.guard policy active origin q m (requests k L) theta cap draw labels = true)
    (tau : ℝ) (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau)
    (lam : ℝ) (hlam : 0 ≤ lam) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L) :
    let t := dataTargets hk q chores active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold lam
    (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ k * targetBudget k q L theta tau lam := by
  dsimp only
  rw [targets_execute]
  cases chores
  · have h := actual_cake_targets μ policy hpolicy active origin hgood hpositive hk old hold
      q m L draw theta htheta cap labels hpass tau htau hnear lam hlam pi threshold
    exact ⟨fun j => (h.1 j).1, h.2⟩
  · have h := actual_chore_targets μ policy hpolicy active origin hgood hpositive hk old hold
      q m L draw theta htheta cap labels hpass tau htau hnear lam hlam pi threshold
    exact ⟨fun j => (h.1 j).1, h.2⟩

/-- No assumed successful rounding, correction or probability bound occurs
here: the actual Boolean guard and old raw near-EF inequalities suffice. -/
theorem approved_checks (hk : 2 ≤ k) (chores : Bool) (old : Fin k → State n)
    (hold : ∀ j, WellFormed μ (old j)) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam tau : ℝ)
    (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L)
    (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau) (hlam : 0 ≤ lam)
    (heta : cellCap q theta ≤ eta) (hbudget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
    (happroved : approved hk chores active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta cap lam labels pi threshold = true) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    Checks μ active (UpperGridData.reserve data theta labels) (UpperGridData.cuts data)
      (dataTargets hk q chores active origin old data L theta labels pi threshold lam) eta
      (reserveCells (UpperGridData.parent data) theta labels) cap := by
  have hpass := ((approved_iff hk chores active origin old _ L theta cap lam labels pi threshold).mp happroved).1
  rw [UpperGridData.guard_execute] at hpass
  have hf := UpperLogicalPreparationGuard.passing_facts μ policy hpolicy active origin hgood hpositive
    q m (requests k L) theta htheta cap draw labels hpass
  have he := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  have ht := actual_targets μ policy hpolicy active origin hgood hpositive hk chores old hold q m L draw
    theta htheta cap labels hpass tau htau hnear lam hlam pi threshold
  refine ⟨hf.wellFormed, he.1, he.2, UpperCommonGrid.grid_monotone _, hf.separated,
    hf.positive, ?_, ht.1, ht.2.trans_lt hbudget, hf.empty_outside, hf.count_le⟩
  intro i e
  exact (hf.table_small i e).trans heta

end Actual

end EnvyFreeResearch.Full.UpperRepairPreparationChecks
