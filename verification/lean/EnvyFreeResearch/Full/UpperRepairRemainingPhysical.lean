import EnvyFreeResearch.Full.UpperRepairRemaining

/-! The actual reconstructed Repair residue is the full original buffer
minus its literal seed and payment unions, with a truthful recorded cache. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairRemaining

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperLogicalCells

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
  (hbudget : 2 * (jobCount k * L) < q + 1)
  (theta : I) (cap eta lam : ℝ) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (tape : Fin k → UpperCircular.Circle)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => UpperGridData.reserve d theta labels
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta labels pi threshold lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "reserved" => reserveCells (UpperGridData.parent d) theta labels
local notation "seeds" => UpperRepairSeedIndices.indices hk active origin d L theta labels pi threshold
local notation "seedSet" => seedUnion (seedSystem hk policy active origin q m L draw theta labels pi)
  (seedCells hk policy active origin q m L draw theta labels pi) threshold
local notation "payments" => ⋃ j, domain (paymentState stage j).cells

variable (hpass : UpperLogicalPreparationGuard.guard policy active origin q m (requests k L) theta cap draw labels = true)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)))
  (hc : Checks μ active R cuts targets eta selected cap)
  (hrun : stage.2.2 = false)

include hpolicy hgood hpositive in
theorem selected_seeds_eq :
    (⋃ j, selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) (seeds j)) = seedSet := by
  apply iUnion_congr
  intro j
  rw [UpperRepairSeedIndices.selected_seed μ policy hpolicy active origin hgood hpositive,
    dataSeedState_domain μ policy hpolicy active origin hgood hpositive]

include hpolicy hgood hpositive hc hrun in
theorem final_selected_complement :
    domain stage.2.1.cells = selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved \ payments := by
  rw [UpperRepairSeedIndices.selected_reserve μ policy hpolicy active origin hgood hpositive]
  exact final_complement_paymentStates μ policy active R cuts targets eta lam cap selected hc tape hrun

include hpolicy hgood hpositive hbudget hpass hc hrun in
theorem remaining_domain :
    domain (remaining hk active origin d L theta labels pi threshold stage.2.1).cells =
      domain origin.cells \ (seedSet ∪ payments) := by
  have hwhole := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hzero := (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
  have hfinal := final_selected_complement μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    theta cap eta lam labels pi threshold tape selected hc hrun
  have hseed := selected_seeds_eq μ policy hpolicy hk active origin hgood hpositive q m L draw theta labels pi threshold
  have hreserve := UpperRepairSeedIndices.selected_reserve μ policy hpolicy active origin hgood hpositive q m draw theta labels
  have hp : payments ⊆ selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved := by
    rw [hreserve]
    exact iUnion_subset (fun j => paymentState_subset policy active R cuts targets eta lam tape hrun j)
  have hd : Disjoint (⋃ j, selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) (seeds j))
      (selectedUnion (cell (domain (UpperGridData.aligned d).cells) cuts) reserved) := by
    rw [hseed, hreserve, UpperGridData.reserve_execute]
    exact seeds_avoid_reserve μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget theta cap labels hpass pi threshold
  have h := UpperRepairResidue.finish_domain (UpperGridData.aligned d) cuts hwhole.2.1 hzero
    (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw)
    reserved seeds stage.2.1 payments hfinal hd hp
  rw [hseed] at h
  simpa only [remaining, UpperGridData.aligned_execute, UpperGridCache.aligned_domain] using h

include hpolicy hinj hgood hpositive heta hlam hsize hmargin hc hrun in
theorem remaining_wellFormed :
    WellFormed μ (remaining hk active origin d L theta labels pi threshold stage.2.1) := by
  have hwhole := UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw
  have hf := stage_recording μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc tape
  exact UpperRepairResidue.finish_wellFormed μ (UpperGridData.aligned d) hwhole cuts
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (UpperCommonGrid.grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw)
    reserved seeds stage.2.1 hf.1 payments
    (final_selected_complement μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      theta cap eta lam labels pi threshold tape selected hc hrun) hf.2.1

end EnvyFreeResearch.Full.UpperRepairRemaining
