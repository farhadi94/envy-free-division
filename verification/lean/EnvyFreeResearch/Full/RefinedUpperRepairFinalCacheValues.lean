import EnvyFreeResearch.Full.RefinedUpperRepairFinalCache
import EnvyFreeResearch.Full.RefinedUpperRepairFinalCacheSpending

/-! The concrete recorded payment states have the same exact values and
literal disjointness as the accepted correction output lists. -/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.RefinedUpperRepairFinalCache

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  RefinedUpperCorrectionSetup RefinedUpperCorrectionOutcome RefinedUpperCorrectionAccepted UpperCorrectionTrace
  RefinedUpperCorrectionDisjoint UpperCorrectionPieces UpperPreparedEnvelopeMean UpperCircularStage


variable {n k m r : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam N : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4 * (k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
  (tape : Fin k → Fin r → UpperCircular.Circle)
  (hrun : (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)

include hrun in
theorem paymentState_subset (j : Fin k) :
    domain (paymentState (executeStage policy active reserve cuts t eta lam tape) j).cells ⊆ domain reserve.cells := by
  rw [paymentState_domain, executeStage_output, RefinedUpperCorrectionOutcome.output, domain_append]
  apply union_subset
  · intro x hx
    obtain ⟨c, hc', hx⟩ := mem_domain.mp hx
    exact mem_domain.mpr ⟨c, (List.mem_filter.mp hc').1, hx⟩
  · have hl : (corrections policy active reserve cuts t eta lam tape).length = k :=
      (RefinedUpperBatchLoop.successful_outputs policy (tasks active reserve cuts t eta lam)
        (startState active reserve cuts t eta).current tape hrun).1
    have hj := getD_mem (corrections policy active reserve cuts t eta lam tape) [] j.val (by rw [hl]; exact j.isLt)
    apply (payments_domain_subset _ _ _ hj).trans
    intro x hx
    obtain ⟨c, hc', hx⟩ := mem_domain.mp hx
    exact mem_domain.mpr ⟨c, (List.mem_filter.mp hc').1, hx⟩

include heta hc hrun in
theorem paymentState_disjoint : Pairwise (fun i j => Disjoint
    (domain (paymentState (executeStage policy active reserve cuts t eta lam tape) i).cells)
    (domain (paymentState (executeStage policy active reserve cuts t eta lam tape) j).cells)) := by
  intro i j hij
  rw [paymentState_domain, paymentState_domain, executeStage_output]
  exact output_disjoint μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive
    t eta lam heta hc.small hc.targets hc.sum policy tape hrun hij

include hpolicy hinj heta hsize hmargin hc hrun in
theorem paymentState_values (j : Fin k) :
    (μ (active j)).real (domain (paymentState (executeStage policy active reserve cuts t eta lam tape) j).cells) /
        (μ (active j)).real (domain reserve.cells) = t j ∧
      ∀ i, |(μ (active i)).real (domain (paymentState (executeStage policy active reserve cuts t eta lam tape) j).cells) /
        (μ (active i)).real (domain reserve.cells) - t j| ≤ lam * UpperPayments.cellGap (table active reserve cuts) i j := by
  rw [paymentState_domain, executeStage_output]
  have h := output_values μ active hinj reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive
    t eta lam heta hc.small hc.targets hc.sum hsize hmargin policy hpolicy tape hrun j
  refine ⟨?_, h.2⟩
  rw [h.1, mul_div_cancel_right₀ _ (hc.positive j).ne']

include hc hrun in
theorem final_complement_paymentStates :
    domain (executeStage policy active reserve cuts t eta lam tape).2.1.cells =
      domain reserve.cells \ ⋃ j, domain (paymentState (executeStage policy active reserve cuts t eta lam tape) j).cells := by
  simp_rw [paymentState_domain, executeStage_output]
  exact RefinedUpperCorrectionSpending.final_domain_complement μ policy active reserve cuts t eta lam N selected hc tape hrun

end EnvyFreeResearch.Full.RefinedUpperRepairFinalCache
