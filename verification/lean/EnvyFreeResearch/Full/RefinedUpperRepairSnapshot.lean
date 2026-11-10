import EnvyFreeResearch.Full.RefinedUpperRepairOutputMeasurable
import EnvyFreeResearch.Full.RefinedUpperRepairCorrespondence
import EnvyFreeResearch.Full.RefinedUpperRepairAllocationPhysical
import EnvyFreeResearch.Full.RefinedUpperRepairPreparationChecks
import EnvyFreeResearch.Full.UpperSnapshotContrast

/-! The contrast lemma's joining and error premises follow from the actual
successful ordinary Repair execution. The error is a pure recorded-cache
quantity, defined and measurable on every tape, including rejection. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairSnapshot

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  RefinedUpperRepairFinalCache UpperPreparedEnvelopeMean UpperRepairPreparationChecks UpperRepairTrialProgram
  RefinedUpperPreparation RefinedUpperRepairAllocation UpperSnapshotContrast

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
  (q m L : ℕ) (hparent : 4 * (jobCount k * L) ≤ q + 1)
  (cap eta lam tau : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4*(k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau)
  (hcell : 2/(q+1 : ℝ) ≤ eta)
  (htarget : (k : ℝ)*RefinedUpperRepairPreparationChecks.targetBudget k q L tau eta lam < 1/16)
  (hcount : (UpperRecordedQuantiles.count (Agent := Fin k) q+m+1 : ℝ) ≤ cap)
  (draw : Fin m → Fin k × I) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k-1+1) → Fin (L+1)) {r : ℕ} (tape : Fin k → Fin r → UpperCircular.Circle)
  (hsuccess : (RefinedUpperRepairProgram.execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 = false)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => dataRetained active origin d L
local notation "cuts" => UpperGridData.cuts d
local notation "prepared" => RefinedUpperPreparationProgram.finish hk chores active origin old d L pi threshold
local notation "targets" => RefinedUpperRepairTargets.targets chores active prepared eta lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "selected" => RefinedUpperRepairSeedIndices.reserved active origin d L
local notation "V" => dataMatrix hk active origin old d L pi threshold
local notation "actual" => RefinedUpperRepairProgram.execute policy hk chores active origin old q m L draw pi threshold eta lam tape
local notation "Z" => normalizedValues (fun i => μ (active i)) (domain (R).cells) (fun j => domain (actual.1 j).cells)
local notation "E" => recordedError active R targets stage

include hpolicy hinj hgood hpositive hold holdbuffer hparent heta hlam hsize hmargin
  htau hnear hcell htarget hcount hsuccess in
theorem successful_joining :
    (∀ i j, Z i j = paid V (assignment chores V) targets i j + E i j) ∧
      (∀ i j, |E i j| ≤ signedGap chores Z i j) ∧ (∀ i, E i i = 0) := by
  obtain ⟨ha, he, hs⟩ := RefinedUpperRepairProgram.accepted_output policy hk chores active origin old q m L
    draw pi threshold eta lam tape hsuccess
  have hc := RefinedUpperRepairPreparationChecks.actual_checks μ policy hpolicy active origin hgood hpositive hk chores old hold
    q m L draw hparent tau eta lam cap htau hnear hlam hcell htarget hcount pi threshold
  have hb : 2*(jobCount k*L) < q+1 := by omega
  have hcycle : cycleReject chores V (dataDisagreement active origin d L) lam = false := by
    change (!cycleReject chores V (dataDisagreement active origin d L) lam) = true at ha
    cases h : cycleReject chores V (dataDisagreement active origin d L) lam <;> simp_all
  have heval (i j) : E i j =
      (μ (active i)).real (domain (paymentState stage j).cells) / (μ (active i)).real (domain (R).cells) - targets j := by
    rw [recordedError, total_correct μ _
      (paymentState_wellFormed μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc tape hs j),
      total_correct μ R hc.wellFormed]
  have hpay := paymentState_values μ policy hpolicy active hinj R cuts targets eta lam cap
    heta hsize hmargin selected hc tape hs
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [heval, he]
    simp only [normalizedValues, Prod.fst]
    have hv := allocation_values μ policy hpolicy hk chores active origin hgood hpositive old hold holdbuffer q m L draw
      hb eta lam pi threshold tape hs i j
    change _ = (V i (assignment chores V j) + targets j) + _
    calc
      _ = V i (assignment chores V j) + (μ (active i)).real (domain (paymentState stage j).cells) /
          (μ (active i)).real (domain (R).cells) := hv
      _ = _ := by ring
  · intro i j
    have hm := allocation_margin μ policy hpolicy hk chores active hinj origin hgood hpositive old hold holdbuffer q m L draw
      hb cap eta lam pi threshold tape heta hsize hmargin selected hc hs hcycle i j
    rw [heval]
    apply ((hpay j).2 i).trans
    rw [he]
    exact hm
  · intro i
    rw [heval, (hpay i).1, sub_self]

include hpolicy hgood hpositive hparent in
theorem retained_half (i : Fin k) :
    (1/2 : ℝ)*(μ (active i)).real (domain origin.cells) ≤ (μ (active i)).real (domain (R).cells) := by
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using
    dataRetained_half μ policy hpolicy active origin hgood hpositive q m L draw hparent i

end EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
