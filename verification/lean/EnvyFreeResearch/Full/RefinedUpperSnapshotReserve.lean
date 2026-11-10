import EnvyFreeResearch.Full.RefinedUpperPreparationFixed
import EnvyFreeResearch.Full.RefinedUpperRepairSnapshotConfigured
import EnvyFreeResearch.Full.UpperSnapshotCandidatesReserveContrast

/-! Actual candidate contrast after every fresh deterministic preparation.
The new reserve is always a subset of the candidate buffer and retains at
least half its value; no successful-branch reserve guard is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates RefinedUpperRepairSnapshot UpperSnapshotContrast RefinedUpperPreparation
variable {n k : ℕ} [Nonempty (Fin k)]

set_option maxHeartbeats 1500000 in
theorem freshReserve_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) :
    Measurable (prepReserve policy active origin : Preparation n k → State n) := by
  have hd : Measurable (prepData policy active origin) :=
    RefinedUpperPreparation.prepare_fixed_measurable policy hmeas active origin
      (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n)
  exact dataRetained_measurable active (fun _ => origin) (prepData policy active origin)
    (RefinedUpperRepair.repeats n) measurable_const hd

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem freshReserve_wellFormed (x : Preparation n k) :
    WellFormed μ (prepReserve policy active origin x) :=
  RefinedUpperRepairPreparationChecks.data_wellFormed μ policy hpolicy active origin hgood hpositive
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) (RefinedUpperRepair.repeats n) x

theorem freshReserve_subset (x : Preparation n k) :
    domain (prepReserve policy active origin x).cells ⊆ domain origin.cells := by
  unfold prepReserve prepData
  rw [dataRetained_execute]
  exact UpperLogicalPreparation.reserveState_subset μ policy hpolicy active origin hgood hpositive
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) x 0 _

theorem freshReserve_half (hinj : Function.Injective active) (x : Preparation n k) (i : Fin k) :
    (1/2 : ℝ)*(μ (active i)).real (domain origin.cells) ≤
      (μ (active i)).real (domain (prepReserve policy active origin x).cells) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := UpperRepairParameters.scale_large n
  have he : (1 : ℝ) ≤ UpperRepairParameters.logarithm (UpperRepairParameters.scale n) := by
    exact_mod_cast UpperRepairParameters.logarithm_positive hs
  exact RefinedUpperRepairSnapshot.retained_half μ policy hpolicy active origin hgood hpositive
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) (RefinedUpperRepair.repeats n)
    (RefinedUpperRepairParameters.parent_budget hs he (UpperRepairParameters.active_scale n k hkn)) x i

theorem large_baseline (hinj : Function.Injective active) (hk : 3 ≤ k) (q m : ℕ)
    (draw : Fin m → Fin k × I) (cutter : Fin k)
    (hbuffer : WellFormed μ (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter))
    (hbufpos : ∀ i, 0 < (μ (active i)).real
      (domain (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter).cells))
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin
      (UpperGridMerge.prepare policy active origin q m draw)) cutter)
    (x : Preparation n k) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let buffer := candidateBuffer (by omega) active origin data cutter
    let reserve := prepReserve policy active buffer x
    let choice := candidateChoice hk active origin data cutter reserve
    selectedDistance (by omega) (UpperGridData.table active origin data) cutter /
      (3*(UpperRecordedQuantiles.count (Agent := Fin k) q+m+1 : ℕ)) ≤
      contrast (prepOld policy active buffer (candidateOld (by omega) active origin data cutter) x)
        choice.1.1 choice.1.2 choice.2.1 choice.2.2 := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let buffer := candidateBuffer (by omega) active origin data cutter
  have hpos (i : Fin k) : 0 < (μ (active i)).real (domain (prepReserve policy active buffer x).cells) :=
    (mul_pos (by norm_num : (0 : ℝ)<1/2) (hbufpos i)).trans_le
      (freshReserve_half μ policy hpolicy active buffer hbuffer hbufpos hinj x i)
  have hupper (i : Fin k) : (μ (active i)).real (domain (prepReserve policy active buffer x).cells) ≤
      3*(1 : ℝ)/2*(μ (active i)).real (domain buffer.cells) := by
    have h := measureReal_mono (μ := μ (active i))
      (freshReserve_subset μ policy hpolicy active buffer hbuffer hbufpos x) (measure_ne_top _ _)
    linarith [hbufpos i]
  have hb := recorded_candidate_contrast μ policy hpolicy active origin hgood hpositive hk q m draw cutter
    (prepReserve policy active buffer x)
    (freshReserve_wellFormed μ policy hpolicy active buffer hbuffer hbufpos x) hpos 1 (by norm_num) hupper hD
  simpa only [mul_one,prepOld,buffer,data] using hb

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
