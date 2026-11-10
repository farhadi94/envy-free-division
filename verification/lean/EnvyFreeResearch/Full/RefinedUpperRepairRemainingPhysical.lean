import EnvyFreeResearch.Full.RefinedUpperRepairRemaining
import EnvyFreeResearch.Full.RefinedUpperRepairTargets
import EnvyFreeResearch.Full.RefinedUpperRepairFinalCacheValues

/-! The actual reconstructed Repair residue is the full original buffer
minus its literal seed and payment unions, with a truthful recorded cache. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairRemaining

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation RefinedUpperPreparation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  UpperPreparedEnvelopeMean UpperLogicalCells

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
local notation "reserved" => RefinedUpperRepairSeedIndices.reserved active origin d L
local notation "seeds" => RefinedUpperRepairSeedIndices.indices hk active origin d L pi threshold
local notation "seedSet" => seedUnion (seedSystem hk policy active origin q m L draw pi)
  (seedCells hk policy active origin q m L draw pi) threshold
local notation "payments" => ⋃ j, domain (paymentState stage j).cells

variable (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4*(k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)))
  (hc : Checks μ active R cuts targets eta selected cap)
  (hrun : stage.2.2 = false)

include hpolicy hgood hpositive in
theorem selected_seeds_eq :
    (⋃ j, selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) (seeds j)) = seedSet := by
  apply iUnion_congr
  intro j
  rw [RefinedUpperRepairSeedIndices.selected_seed μ policy hpolicy active origin hgood hpositive,
    RefinedUpperPreparation.dataSeedState_domain μ policy hpolicy active origin hgood hpositive]

include hpolicy hgood hpositive hc hrun in
theorem final_selected_complement :
    domain stage.2.1.cells = selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved \ payments := by
  rw [RefinedUpperRepairSeedIndices.selected_reserve μ policy hpolicy active origin hgood hpositive]
  exact final_complement_paymentStates μ policy active R cuts targets eta lam cap selected hc tape hrun

include hpolicy hgood hpositive hbudget hc hrun in
theorem remaining_domain :
    domain (remaining hk active origin d L pi threshold stage.2.1).cells =
      domain origin.cells \ (seedSet ∪ payments) := by
  have hwhole := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hzero := (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  have hfinal := final_selected_complement μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    cap eta lam pi threshold tape selected hc hrun
  have hseed := selected_seeds_eq μ policy hpolicy hk active origin hgood hpositive q m L draw pi threshold
  have hreserve := RefinedUpperRepairSeedIndices.selected_reserve μ policy hpolicy active origin hgood hpositive q m L draw
  have hp : payments ⊆ selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved := by
    rw [hreserve]
    exact iUnion_subset (fun j => paymentState_subset policy active R cuts targets eta lam tape hrun j)
  have hd : Disjoint (⋃ j, selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) (seeds j))
      (selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved) := by
    rw [hseed,hreserve]
    exact UpperLogicalIsolation.seedUnion_disjoint _ _ _ (fun j a =>
      RefinedUpperPreparation.witnesses_retained_disjoint μ policy hpolicy active origin hgood hpositive
        q m L draw hbudget _ a) threshold
  have h := UpperRepairResidue.finish_domain (UpperGridData.aligned d) cuts hwhole.2.1 hzero
    (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw)
    reserved seeds stage.2.1 payments hfinal hd hp
  rw [hseed] at h
  simpa only [remaining, UpperGridData.aligned_execute, UpperGridCache.aligned_domain] using h

include hpolicy hinj hgood hpositive heta hlam hsize hmargin hc hrun in
theorem remaining_wellFormed :
    WellFormed μ (remaining hk active origin d L pi threshold stage.2.1) := by
  have hwhole := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hf := stage_recording μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc tape
  exact UpperRepairResidue.finish_wellFormed μ (UpperGridData.aligned d) hwhole cuts
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw)
    reserved seeds stage.2.1 hf.1 payments
    (final_selected_complement μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      cap eta lam pi threshold tape selected hc hrun) hf.2.1

end EnvyFreeResearch.Full.RefinedUpperRepairRemaining
