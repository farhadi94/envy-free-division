import EnvyFreeResearch.Full.UpperGlobalProtocolProgress
import EnvyFreeResearch.Full.UpperGlobalPendingMassReady

/-! The actual final Repair, at the manuscript parameters, strictly increases
the saved global potential. Its local correctness and transport witnesses
are obtained from its execution, rather than assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperCircularStage GlobalCompletion
variable {n : ℕ}

theorem actual_nearError_le_quarter (n : ℕ) : UpperRepair.nearError n ≤ 1/4 := by
  have hs := UpperRepairParameters.scale_large n
  have hell : (1 : ℝ) ≤ UpperRepairParameters.logarithm (UpperRepairParameters.scale n) := by
    exact_mod_cast UpperRepairParameters.logarithm_positive hs
  have hone := UpperRepairParameters.denominator_ge_one hs hell 10 1
  simp only [pow_one] at hone
  change 1 / (4 * (UpperRepairParameters.scale n : ℝ)^10 *
    UpperRepairParameters.logarithm (UpperRepairParameters.scale n)) ≤ 1/4
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

theorem actual_finish_progress
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (hvalid : Valid (if chores then .chore else .cake) (p.anchor.table μ))
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (hnear : UpperRepairPreparationChecks.Near chores μ (enumerate p.anchor.active)
      p.buffer (localEndowments p) (UpperRepair.nearError n))
    (hedge : p.anchor.edge (if chores then .chore else .cake) p.witness p.target)
    (hstrong : (2-UpperRepair.nearError n) * (μ p.witness).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments) p.witness p.target)
    (tape : UpperRepair.Tape n p.anchor.active.card)
    (hsuccess : (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) tape).2.2 = false) :
    let final := finish p (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) tape)
    final.Committed μ (if chores then .chore else .cake) whole ∧
      p.anchor.cachedPotential (if chores then .chore else .cake) + 1 ≤
        final.cachedPotential (if chores then .chore else .cake) := by
  dsimp only
  have hc := (actual_finish μ whole p hp policy hpolicy hk chores hvalid hpositive hnear tape hsuccess).1
  obtain ⟨w⟩ := actual_finish_witness μ whole p hp policy hpolicy hk chores hpositive hnear tape hsuccess
  have facts := UpperRepair.success_facts μ policy hpolicy hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p)
    (localEndowments_wf μ whole p hp) hnear (localEndowments_pair μ whole p hp)
    (localEndowments_separate μ whole p hp) (localEndowments_history p) tape hsuccess
  obtain ⟨b,hb⟩ := enumerate_preimage p.anchor.active p.witness hedge.1
  obtain ⟨h,hh⟩ := enumerate_preimage p.anchor.active p.target hedge.2.1
  have hs : (2-UpperRepair.nearError n) *
      (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments)
        (enumerate p.anchor.active b) (enumerate p.anchor.active h) := by
    simpa only [hb,hh] using hstrong
  have he : p.anchor.edge (if chores then .chore else .cake)
      (enumerate p.anchor.active b) (enumerate p.anchor.active h) := by
    simpa only [hb,hh] using hedge
  have hg := success_potential_growth μ whole p hp chores hvalid _ facts w b h
    (UpperRepair.nearError n) ((actual_nearError_le_quarter n).trans (by norm_num))
    (hpositive b) he hs
  refine ⟨hc,?_⟩
  rw [cachedPotential_correct μ whole p.anchor hp.anchor,
    cachedPotential_correct μ whole _ hc.1]
  exact hg

/-- The cached transfer checks themselves discharge both the final Repair's
near-EF hypothesis and the strong comparison used for strict progress. -/
theorem actual_cached_finish_progress
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (hvalid : Valid (if chores then .chore else .cake) (p.anchor.table μ))
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (hH : ActiveEF (if chores then .chore else .cake) (value μ p.shrunk) p.anchor.active)
    (hX : ActiveEF (if chores then .chore else .cake) (value μ p.snapshot) p.anchor.active)
    (hown : ∀ i ∈ p.anchor.active,
      margin (if chores then .chore else .cake) (fun a b => total (p.snapshot b) a)
        i (p.permutation i) ≤ UpperRepair.nearError n * total p.buffer i)
    (hedge : p.anchor.edge (if chores then .chore else .cake) p.witness p.target)
    (hlarge : 2 * total p.buffer p.witness ≤
      margin (if chores then .chore else .cake) (fun a b => total (p.snapshot b) a)
        p.witness (p.permutation p.target))
    (tape : UpperRepair.Tape n p.anchor.active.card)
    (hsuccess : (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) tape).2.2 = false) :
    let final := finish p (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) tape)
    final.Committed μ (if chores then .chore else .cake) whole ∧
      p.anchor.cachedPotential (if chores then .chore else .cake) + 1 ≤
        final.cachedPotential (if chores then .chore else .cake) := by
  have hW : ActiveEF (if chores then .chore else .cake)
      (value μ p.anchor.bundles) p.anchor.active := fun i _ j _ => hvalid.2.2.1 i j
  have hi := pending_cached_repair_input μ whole p hp chores (enumerate p.anchor.active)
    (enumerate_mem _) (UpperRepair.nearError n) hW hH hX hown hedge.1 hedge.2.1 hlarge
  exact actual_finish_progress μ whole p hp policy hpolicy hk chores hvalid hpositive
    hi.1 hedge hi.2 tape hsuccess

end EnvyFreeResearch.Full.UpperGlobalPhysicalFinish

