import EnvyFreeResearch.Full.UpperRepairOutputMeasurable
import EnvyFreeResearch.Full.UpperSnapshotContrast

/-! The contrast lemma's joining and error premises follow from the actual
successful ordinary Repair execution. The error is a pure recorded-cache
quantity, defined and measurable on every tape, including rejection. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperRepairPreparationChecks UpperRepairTrialProgram
  UpperRepairTrialLaw UpperRepairAllocation UpperSnapshotContrast

variable {n k q m L : ℕ} [Nonempty (Fin k)]

def recordedError (active : Fin k → Fin n) (reserve : State n) (t : Fin k → ℝ)
    (result : Result n k) (i j : Fin k) : ℝ :=
  total (paymentState result j) (active i) / total reserve (active i) - t j

theorem recordedError_measurable {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (reserve : X → State n) (t : X → Fin k → ℝ)
    (result : X → Result n k) (hreserve : Measurable reserve)
    (ht : ∀ j, Measurable (fun x => t x j)) (hresult : Measurable result) (i j : Fin k) :
    Measurable (fun x => recordedError active (reserve x) (t x) (result x) i j) :=
  ((total_measurable _ (fun _ => active i) (paymentState_measurable result hresult j) measurable_const).div
    (total_measurable reserve (fun _ => active i) hreserve measurable_const)).sub (ht j)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (q m L : ℕ) (hrepresentatives : 2 * (jobCount k * L) < q + 1)
  (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam tau : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau)
  (hcell : cellCap q theta ≤ eta) (htarget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
  (p : Tape k q m L)
  (hsuccess : (UpperRepairProgram.execute policy hk chores active origin old q m L theta cap eta lam p).2.2 = false)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m p.2.1.1
local notation "R" => UpperGridData.reserve d theta p.1
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam
local notation "stage" => executeStage policy active R cuts targets eta lam p.2.2
local notation "selected" => reserveCells (UpperGridData.parent d) theta p.1
local notation "V" => dataMatrix hk active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2
local notation "actual" => UpperRepairProgram.execute policy hk chores active origin old q m L theta cap eta lam p
local notation "Z" => normalizedValues (fun i => μ (active i)) (domain (R).cells) (fun j => domain (actual.1 j).cells)
local notation "E" => recordedError active R targets stage

include hpolicy hinj hgood hpositive hold holdbuffer hrepresentatives htheta heta hlam hsize hmargin
  htau hnear hcell htarget hsuccess in
theorem successful_joining :
    (∀ i j, Z i j = paid V (assignment chores V) targets i j + E i j) ∧
      (∀ i j, |E i j| ≤ signedGap chores Z i j) ∧ (∀ i, E i i = 0) := by
  obtain ⟨ha, he, hs, hu⟩ := UpperRepairProgram.accepted_output policy hk chores active origin old q m L
    theta cap eta lam p hsuccess
  simp only [UpperRepairTrialLaw.data] at ha he hs hu
  have hc := approved_checks μ policy hpolicy active origin hgood hpositive hk chores old hold q m L p.2.1.1
    theta htheta cap eta lam tau p.1 p.2.1.2.1 p.2.1.2.2 htau hnear hlam hcell htarget ha
  have hap := (approved_iff hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2).mp ha
  have hp := hap.1
  rw [UpperGridData.guard_execute] at hp
  have heval (i j) : E i j =
      (μ (active i)).real (domain (paymentState stage j).cells) / (μ (active i)).real (domain (R).cells) - targets j := by
    rw [recordedError, total_correct μ _
      (paymentState_wellFormed μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc p.2.2 hs j),
      total_correct μ R hc.wellFormed]
  have hpay := paymentState_values μ policy hpolicy active hinj R cuts targets eta lam cap
    heta hsize hmargin selected hc p.2.2 hs
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [heval, he]
    simp only [normalizedValues, Prod.fst]
    have hv := allocation_values μ policy hpolicy hk chores active origin hgood hpositive old hold holdbuffer q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp hs i j
    change _ = (V i (assignment chores V j) + targets j) + _
    linarith only [hv]
  · intro i j
    have hm := allocation_margin μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer q m L p.2.1.1
      hrepresentatives theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hp heta hsize hmargin selected hc hs hap.2 i j
    rw [heval]
    apply ((hpay j).2 i).trans
    rw [he]
    exact hm
  · intro i
    rw [heval, (hpay i).1, sub_self]

include hpolicy hgood hpositive hsuccess in
theorem successful_reserve (i : Fin k) :
    (theta : ℝ) / 2 * (μ (active i)).real (domain origin.cells) ≤ (μ (active i)).real (domain (R).cells) ∧
      (μ (active i)).real (domain (R).cells) ≤ 3 * (theta : ℝ) / 2 * (μ (active i)).real (domain origin.cells) := by
  obtain ⟨ha, he, hs, hu⟩ := UpperRepairProgram.accepted_output policy hk chores active origin old q m L
    theta cap eta lam p hsuccess
  simp only [UpperRepairTrialLaw.data] at ha he hs hu
  have hp := ((approved_iff hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2).mp ha).1
  rw [UpperGridData.guard_execute] at hp
  exact UpperSnapshotCandidates.snapshotGuard_mass μ policy hpolicy active origin hgood hpositive q m (requests k L)
    theta cap p.2.1.1 p.1 (Bool.and_eq_true_iff.mpr ⟨hp, hu⟩) i

end EnvyFreeResearch.Full.UpperRepairSnapshot
