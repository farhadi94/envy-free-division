import EnvyFreeResearch.Full.UpperRepairCorrespondence
import EnvyFreeResearch.Full.UpperRepairMaterial
import EnvyFreeResearch.Full.UpperRepairSpending
import EnvyFreeResearch.Full.UpperRepairPreparationChecks

/-! Successful ordinary Repair produces actual recorded, disjoint,
envy-free pieces and preserves all material with a large positive residue.
Every correction check is derived from the actual trial and raw near-EF
input; none is an assumed successful subroutine contract. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperRepairPreparationChecks UpperRepairTrialProgram
  UpperRepairTrialLaw UpperRepairAllocation

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
  (q m L : ℕ) (hrepresentatives : 2 * (jobCount k * L) < q + 1)
  (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam tau : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (hseed : (jobCount k : ℝ) * L / (q + 1 : ℝ) < 1 / 8)
  (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau)
  (hcell : cellCap q theta ≤ eta) (htarget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
  (p : Tape k q m L)
  (hsuccess : (execute policy hk chores active origin old q m L theta cap eta lam p).2.2 = false)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m p.2.1.1
local notation "R" => UpperGridData.reserve d theta p.1
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam
local notation "stage" => executeStage policy active R cuts targets eta lam p.2.2
local notation "selected" => reserveCells (UpperGridData.parent d) theta p.1
local notation "A" => dataDisagreement active d theta p.1

include hpolicy hinj hgood hpositive hold holdpair holdbuffer holdHistory hrepresentatives htheta
  heta hlam hsize hmargin hseed htau hnear hcell htarget hsuccess in
theorem success_facts :
    SuccessFacts μ chores active origin old (execute policy hk chores active origin old q m L theta cap eta lam p) := by
  obtain ⟨ha, he, hs, hu⟩ := accepted_output policy hk chores active origin old q m L theta cap eta lam p hsuccess
  simp only [UpperRepairTrialLaw.data] at ha he hs hu
  have hc := approved_checks μ policy hpolicy active origin hgood hpositive hk chores old hold q m L p.2.1.1
    theta htheta cap eta lam tau p.1 p.2.1.2.1 p.2.1.2.2 htau hnear hlam hcell htarget ha
  have hap := (approved_iff hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2).mp ha
  have hp := hap.1
  rw [UpperGridData.guard_execute] at hp
  rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact allocation_wellFormed μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer
      q m L p.2.1.1 hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp
      heta hlam hsize hmargin selected hc hs holdHistory
  · exact UpperRepairRemaining.remaining_wellFormed μ policy hpolicy hk chores active hinj origin hgood hpositive
      old q m L p.2.1.1 theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 heta hlam hsize hmargin selected hc hs
  · exact allocation_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp heta selected hc hs holdpair
  · exact UpperRepairMaterial.residue_disjoint μ policy hpolicy hk chores active origin hgood hpositive old q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp selected hc hs holdbuffer
  · exact UpperRepairMaterial.material_preserved μ policy hpolicy hk chores active origin hgood hpositive old q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp selected hc hs
  · change domain (UpperRepairRemaining.remaining hk active origin d L theta p.1 p.2.1.2.1 p.2.1.2.2 stage.2.1).cells ⊆ domain origin.cells
    rw [UpperRepairRemaining.remaining_domain μ policy hpolicy hk chores active origin hgood hpositive old q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp selected hc hs]
    exact sdiff_subset
  · exact UpperRepairSpending.remaining_mass μ policy hpolicy hk chores active hinj origin hgood hpositive old q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp heta hlam hsize hmargin hseed selected hc hs
  · intro i j
    have hm := allocation_margin μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp heta hsize hmargin selected hc hs hap.2 i j
    have hn : 0 ≤ lam * A i j := mul_nonneg hlam (UpperPayments.cellGap_nonneg _ i j)
    cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm ⊢
    · apply (div_le_div_iff_of_pos_right (hc.positive i)).mp
      linarith
    · apply (div_le_div_iff_of_pos_right (hc.positive i)).mp
      linarith
  · intro j
    rfl

end EnvyFreeResearch.Full.UpperRepairProgram
