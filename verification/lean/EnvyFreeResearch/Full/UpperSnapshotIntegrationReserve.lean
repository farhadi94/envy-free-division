import EnvyFreeResearch.Full.UpperSnapshotCandidatesReserveContrast
import EnvyFreeResearch.Full.UpperRepairSnapshotConfigured

/-! The large recorded candidate supplies the contrast premise for a fresh
Repair, with a measurable explicit choice and the actual reserve checks. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates UpperRepairSnapshot UpperSnapshotContrast UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem freshReserve_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) :
    Measurable (prepReserve policy active origin : Preparation n k → State n) := by
  have hd : Measurable (prepData policy active origin : Preparation n k → _) :=
    UpperLogicalPreparationGuard.fixed_origin_projection_measurable
      (fun z : State n × (Fin (UpperRepair.fine n) → Fin k × I) =>
        UpperGridMerge.prepare policy active z.1 (UpperRepair.coarse n) (UpperRepair.fine n) z.2)
      (UpperGridMerge.prepare_measurable policy hmeas active (UpperRepair.coarse n) (UpperRepair.fine n)) origin
  exact UpperGridData.reserve_measurable (prepData policy active origin) (UpperRepair.reserveMark n)
    Prod.snd hd (fun i => (measurable_pi_apply i).comp measurable_snd)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive in

theorem freshReserve_wellFormed (x : Preparation n k) :
    WellFormed μ (prepReserve policy active origin x) := by
  unfold prepReserve prepData
  rw [UpperGridData.reserve_execute]
  exact UpperLogicalPreparation.reserveState_wellFormed μ policy hpolicy active origin hgood hpositive
    (UpperRepair.coarse n) (UpperRepair.fine n) x.1 (UpperRepair.reserveMark n) x.2

include hpolicy hgood hpositive in
theorem large_baseline (hk : 3 ≤ k) (chores : Bool) (q m : ℕ)
    (draw : Fin m → Fin k × I) (cutter : Fin k)
    (hbuffer : WellFormed μ (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter))
    (hbufpos : ∀ i, 0 < (μ (active i)).real
      (domain (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter).cells))
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin
      (UpperGridMerge.prepare policy active origin q m draw)) cutter)
    (p : UpperRepair.Tape n k)
    (hs : (UpperRepair.execute policy (by omega) chores active
      (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter)
      (candidateOld (by omega) active origin (UpperGridMerge.prepare policy active origin q m draw) cutter) p).2.2 = false) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let buffer := candidateBuffer (by omega) active origin data cutter
    let reserve := prepReserve policy active buffer (view p).1
    let choice := candidateChoice hk active origin data cutter reserve
    (selectedDistance (by omega) (UpperGridData.table active origin data) cutter /
      (3 * (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1 : ℕ))) /
      (UpperRepair.reserveMark n : ℝ) ≤
      contrast (prepOld policy active buffer (candidateOld (by omega) active origin data cutter) (view p).1)
        choice.1.1 choice.1.2 choice.2.1 choice.2.2 := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let buffer := candidateBuffer (by omega) active origin data cutter
  let old := candidateOld (by omega) active origin data cutter
  have hr := original_reserve μ policy hpolicy (by omega) chores active buffer hbuffer hbufpos old p hs
  have htheta : 0 < (UpperRepair.reserveMark n : ℝ) :=
    reserve_positive (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))
  have hpos (i : Fin k) : 0 < (μ (active i)).real
      (domain (prepReserve policy active buffer (view p).1).cells) :=
    lt_of_lt_of_le (mul_pos (div_pos htheta (by norm_num)) (hbufpos i)) (hr i).1
  have hb := recorded_candidate_contrast μ policy hpolicy active origin hgood hpositive hk q m draw cutter
    (prepReserve policy active buffer (view p).1)
    (freshReserve_wellFormed μ policy hpolicy active buffer hbuffer hbufpos _) hpos
    (UpperRepair.reserveMark n) htheta.le (fun i => (hr i).2) hD
  dsimp only [prepOld, buffer, data] at hb ⊢
  have halg (D th M : ℝ) : D / (3 * M) / th = D / (3 * th * M) := by ring
  rw [halg]
  exact hb
end EnvyFreeResearch.Full.UpperSnapshotProtocol
