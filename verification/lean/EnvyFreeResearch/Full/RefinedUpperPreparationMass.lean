import EnvyFreeResearch.Full.RefinedUpperPreparationRetained

/-! Deterministic half-buffer supply and the normalized retained-cell cap. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperGridCells UpperLogicalPreparation Chores
open scoped Classical unitInterval
variable {n : ℕ} {Agent : Type*} [Fintype Agent]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

/-- Selected parents cost at most half the original mass in every row. -/
theorem retainedState_half (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1)))
    (hbudget : 2*removed.card ≤ q+1) (a : Agent) :
    (μ (active a)).real (domain origin.cells)/2 ≤
      (μ (active a)).real (domain (retainedState policy active origin q m draw removed).cells) := by
  have hlow := retainedState_mass_lower μ policy hpolicy active origin hgood hpositive q m draw removed a
  have hcap : (removed.card : ℝ)/(q+1 : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < q+1)).mpr
    have hb : 2*(removed.card : ℝ) ≤ (q+1 : ℝ) := by exact_mod_cast hbudget
    linarith
  rw [total_correct μ origin hgood,
    total_correct μ _ (retainedState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw removed)] at hlow
  have hh : (1/2 : ℝ) ≤ (μ (active a)).real
      (domain (retainedState policy active origin q m draw removed).cells) /
      (μ (active a)).real (domain origin.cells) := by linarith
  have h := (le_div_iff₀ (hpositive a)).mp hh
  linarith

theorem retainedState_positive (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1)))
    (hbudget : 2*removed.card ≤ q+1) (a : Agent) :
    0 < (μ (active a)).real (domain (retainedState policy active origin q m draw removed).cells) :=
  (div_pos (hpositive a) (by norm_num : (0 : ℝ) < 2)).trans_le
    (retainedState_half μ policy hpolicy active origin hgood hpositive q m draw removed hbudget a)

/-- The actual retained cache has cap twice the original coarse cap, even
though the retained domain depends on the entire sampled grid. -/
theorem retainedState_table_cap (q m : ℕ) (draw : Fin m → Agent × I)
    (removed : Finset (Fin (count (Agent := Agent) q + 1)))
    (hbudget : 2*removed.card ≤ q+1) (a : Agent)
    (e : Fin (count (Agent := Agent) q + m + 1)) :
    cachedMass (retainedState policy active origin q m draw removed)
      (UpperGridMerge.cuts policy active origin q m draw) (active a) e /
      total (retainedState policy active origin q m draw removed) (active a) ≤ 2/(q+1 : ℝ) := by
  have hlower := retainedState_half μ policy hpolicy active origin hgood hpositive q m draw removed hbudget a
  have hgoodT := retainedState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw removed
  rw [total_correct μ _ hgoodT]
  unfold retainedState at *
  rw [reserveState_cachedMass μ policy hpolicy active origin hgood hpositive]
  split_ifs
  · have h := renormalized_small _ _ _ (1/(q+1 : ℝ)) 1
      (hpositive a) (by norm_num) (by positivity)
      (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw a e)
      (by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower)
    simpa only [div_one,mul_one_div] using h
  · simp only [zero_div]
    positivity

end EnvyFreeResearch.Full.RefinedUpperPreparation
