import EnvyFreeResearch.Full.RefinedUpperRepairCorrespondence
import EnvyFreeResearch.Full.RefinedUpperRepairMaterial
import EnvyFreeResearch.Full.RefinedUpperRepairSpending
import EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks

/-! Successful ordinary Repair produces actual recorded, disjoint,
envy-free pieces and preserves all material with a large positive residue.
Every correction check is derived from the actual trial and raw near-EF
input; none is an assumed successful subroutine contract. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  UpperPreparedEnvelopeMean RefinedUpperRepairPreparationChecks RefinedUpperRepairTargets
  RefinedUpperPreparation RefinedUpperRepairAllocation

variable {n k : ℕ} [Nonempty (Fin k)]

structure SuccessFacts (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (result : PhysicalResult n k) : Prop where
  allocation_wellFormed : ∀ j, WellFormed μ (result.1 j)
  residue_wellFormed : WellFormed μ result.2.1
  allocation_disjoint : Pairwise (fun i j => Disjoint (domain (result.1 i).cells) (domain (result.1 j).cells))
  residue_disjoint : ∀ j, Disjoint (domain (result.1 j).cells) (domain result.2.1.cells)
  material_preserved : (⋃ j, domain (result.1 j).cells) ∪ domain result.2.1.cells =
    (⋃ j, domain (old j).cells) ∪ domain origin.cells
  residue_subset : domain result.2.1.cells ⊆ domain origin.cells
  residue_mass : ∀ i, (3 / 4 : ℝ) * (μ (active i)).real (domain origin.cells) <
      (μ (active i)).real (domain result.2.1.cells) ∧
    (μ (active i)).real (domain result.2.1.cells) ≤ (μ (active i)).real (domain origin.cells)
  envyFree : ∀ i j, if chores then
      (μ (active i)).real (domain (result.1 i).cells) ≤ (μ (active i)).real (domain (result.1 j).cells)
    else (μ (active i)).real (domain (result.1 j).cells) ≤ (μ (active i)).real (domain (result.1 i).cells)
  common_history : ∀ j, (result.1 j).history = result.2.1.history

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (holdHistory : ∀ j, (old j).history ⊆ origin.history)
  (q m L : ℕ) (hparent : 4 * (jobCount k * L) ≤ q + 1)
  (cap eta lam tau : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4*(k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (hseed : (jobCount k : ℝ) * L / (q + 1 : ℝ) < 1 / 8)
  (htau : 0 ≤ tau) (hnear : UpperRepairPreparationChecks.Near chores μ active origin old tau)
  (hcell : 2/(q+1 : ℝ) ≤ eta) (htarget : (k : ℝ) * targetBudget k q L tau eta lam < 1 / 16)
  (hcount : (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1 : ℝ) ≤ cap)
  (draw : Fin m → Fin k × I) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k-1+1) → Fin (L+1)) {r : ℕ} (tape : Fin k → Fin r → UpperCircular.Circle)
  (hsuccess : (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 = false)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => dataRetained active origin d L
local notation "cuts" => UpperGridData.cuts d
local notation "p" => RefinedUpperPreparationProgram.finish hk chores active origin old d L pi threshold
local notation "targets" => RefinedUpperRepairTargets.targets chores active p eta lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "selected" => RefinedUpperRepairSeedIndices.reserved active origin d L
local notation "A" => dataDisagreement active origin d L
local notation "X" => allocation hk chores active origin old d L pi threshold stage

include hpolicy hinj hgood hpositive hold holdpair holdbuffer holdHistory hparent
  heta hlam hsize hmargin hseed htau hnear hcell htarget hcount hsuccess in
theorem success_facts :
    SuccessFacts μ chores active origin old (execute policy hk chores active origin old q m L draw pi threshold eta lam tape) := by
  obtain ⟨ha, he, hs⟩ := accepted_output policy hk chores active origin old q m L draw pi threshold eta lam tape hsuccess
  change approved chores active p lam = true at ha
  have hc := actual_checks μ policy hpolicy active origin hgood hpositive hk chores old hold q m L draw
    hparent tau eta lam cap htau hnear hlam hcell htarget hcount pi threshold
  have hb : 2*(jobCount k*L) < q+1 := by omega
  have hcycle : cycleReject chores (dataMatrix hk active origin old d L pi threshold) A lam = false := by
    change (!cycleReject chores (dataMatrix hk active origin old d L pi threshold) A lam) = true at ha
    cases h : cycleReject chores (dataMatrix hk active origin old d L pi threshold) A lam <;> simp_all
  rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact allocation_wellFormed μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer
      q m L draw hb cap eta lam pi threshold tape heta hlam hsize hmargin selected hc hs holdHistory
  · exact RefinedUpperRepairRemaining.remaining_wellFormed μ policy hpolicy hk chores active hinj origin hgood hpositive
      old q m L draw cap eta lam pi threshold tape heta hlam hsize hmargin selected hc hs
  · exact allocation_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer q m L draw
      hb cap eta lam pi threshold tape heta selected hc hs holdpair
  · exact RefinedUpperRepairMaterial.residue_disjoint μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      hb cap eta lam pi threshold tape selected hc hs holdbuffer
  · exact RefinedUpperRepairMaterial.material_preserved μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      hb cap eta lam pi threshold tape selected hc hs
  · change domain (RefinedUpperRepairRemaining.remaining hk active origin d L pi threshold stage.2.1).cells ⊆ domain origin.cells
    rw [RefinedUpperRepairRemaining.remaining_domain μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      hb cap eta lam pi threshold tape selected hc hs]
    exact sdiff_subset
  · exact RefinedUpperRepairSpending.remaining_mass μ policy hpolicy hk chores active hinj origin hgood hpositive old q m L draw
      hb cap eta lam pi threshold tape heta hlam hsize hmargin hseed selected hc hs
  · intro i j
    have hm := allocation_margin μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer q m L draw
      hb cap eta lam pi threshold tape heta hsize hmargin selected hc hs hcycle i j
    have hn : 0 ≤ lam * A i j := mul_nonneg hlam (UpperPayments.cellGap_nonneg _ i j)
    change (if chores then (μ (active i)).real (domain (X i).cells) ≤ (μ (active i)).real (domain (X j).cells)
      else (μ (active i)).real (domain (X j).cells) ≤ (μ (active i)).real (domain (X i).cells))
    have hpos : 0 < (μ (active i)).real (domain (R).cells) := hc.positive i
    cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm ⊢
    · apply (div_le_div_iff_of_pos_right hpos).mp
      linarith
    · apply (div_le_div_iff_of_pos_right hpos).mp
      linarith
  · intro j
    rfl

end EnvyFreeResearch.Full.RefinedUpperRepairProgram
