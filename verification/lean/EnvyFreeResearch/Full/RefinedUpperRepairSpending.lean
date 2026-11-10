import EnvyFreeResearch.Full.RefinedUpperRepairRemainingPhysical

/-! Original-buffer value retained by actual successful Repair. Seed and
correction spending are charged together, before subtracting from the full
buffer, for every active original measure. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairSpending

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation RefinedUpperPreparation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  UpperPreparedEnvelopeMean

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
  (hbudget : 2 * (jobCount k * L) < q + 1)
  (cap eta lam : ℝ) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) {r : ℕ} (tape : Fin k → Fin r → UpperCircular.Circle)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => dataRetained active origin d L
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => RefinedUpperRepairTargets.targets chores active
  (RefinedUpperPreparationProgram.finish hk chores active origin old d L pi threshold) eta lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "seedSet" => seedUnion (seedSystem hk policy active origin q m L draw pi)
  (seedCells hk policy active origin q m L draw pi) threshold
local notation "payments" => ⋃ j, domain (paymentState stage j).cells
local notation "B'" => RefinedUpperRepairRemaining.remaining hk active origin d L pi threshold stage.2.1

variable (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4*(k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (hseed : (jobCount k : ℝ) * L / (q + 1 : ℝ) < 1 / 8)
  (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)))
  (hc : Checks μ active R cuts targets eta selected cap) (hrun : stage.2.2 = false)

include hpolicy hinj hgood hpositive heta hlam hsize hmargin hc hrun in
theorem payment_spending (i : Fin k) :
    (μ (active i)).real payments < (μ (active i)).real (domain origin.cells) / 8 := by
  simp_rw [paymentState_domain, executeStage_output]
  exact RefinedUpperCorrectionSpending.output_union_mass_lt_buffer_eighth μ policy hpolicy active hinj R cuts targets
    eta lam cap heta hlam hsize hmargin selected hc tape hrun (domain origin.cells)
    (reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw 0 _) i

include hpolicy hinj hgood hpositive heta hlam hsize hmargin hseed hc hrun in
theorem total_spending (i : Fin k) :
    (μ (active i)).real (seedSet ∪ payments) < (μ (active i)).real (domain origin.cells) / 4 := by
  have hs := RefinedUpperPreparation.seeds_raw_spending μ policy hpolicy active origin hgood hpositive hk q m L draw pi threshold i
  have hs' := mul_lt_mul_of_pos_right hseed (hpositive i)
  have hp := payment_spending μ policy hpolicy hk chores active hinj origin hgood hpositive old q m L draw
    cap eta lam pi threshold tape heta hlam hsize hmargin selected hc hrun i
  have hu := measureReal_union_le (μ := μ (active i)) seedSet payments
  linarith

include hpolicy hinj hgood hpositive hbudget heta hlam hsize hmargin hseed hc hrun in
theorem remaining_mass (i : Fin k) :
    (3 / 4 : ℝ) * (μ (active i)).real (domain origin.cells) < (μ (active i)).real (domain (B').cells) ∧
      (μ (active i)).real (domain (B').cells) ≤ (μ (active i)).real (domain origin.cells) := by
  rw [RefinedUpperRepairRemaining.remaining_domain μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    hbudget cap eta lam pi threshold tape selected hc hrun]
  have hs := total_spending μ policy hpolicy hk chores active hinj origin hgood hpositive old q m L draw
    cap eta lam pi threshold tape heta hlam hsize hmargin hseed selected hc hrun i
  have hd := le_measureReal_sdiff (μ := μ (active i)) (s₁ := domain origin.cells) (s₂ := seedSet ∪ payments)
  exact ⟨by linarith, measureReal_mono sdiff_subset (measure_ne_top _ _)⟩

end EnvyFreeResearch.Full.RefinedUpperRepairSpending
