import EnvyFreeResearch.Full.RefinedUpperSnapshotLarge
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolActualRun

/-! The actual large branch meets the manuscript's common Snapshot threshold
at the original population scales. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
  UpperSnapshotCandidates UpperRepairSnapshot UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem configured_large_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (draw : Fin (RefinedUpperRepair.fine n) → Fin k × I) (cutter : Fin k)
    (hD : RefinedUpperRepair.nearError n /16 ≤ selectedDistance (by omega)
      (UpperGridData.table active origin
        (UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw)) cutter) :
    let data := UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw
    let old := candidateOld (by omega) active origin data cutter
    let buffer := candidateBuffer (by omega) active origin data cutter
    31/64 < (RefinedUpperRepair.law n k).real
      {p | (execute policy (by omega) chores active (margin n) buffer old p).2.2 = false} := by
  have hs := scale_large n
  have hell : (1:ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have hs256 : 256 ≤ scale n := by exact_mod_cast (show (256:ℝ) ≤ scale n from (by norm_num : (256:ℝ) ≤ 2^42).trans hs)
  have he := logarithm_positive hs
  have htau : 0 < RefinedUpperRepair.nearError n := by
    unfold RefinedUpperRepair.nearError RefinedUpperParameterCounts.oldError
    positivity [s_positive hs]
  have hcap := RefinedUpperSnapshotParameters.coarse_cap_small (by omega : 2 ≤ scale n) he
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have ha : 256*k ≤ scale n := by
    have hh := active_scale n k hkn
    exact_mod_cast (show (256:ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α:=ℝ) k])
  have hcount := RefinedUpperParameterCounts.cell_count hs256 he ha (by omega : 1≤k)
  have hsample : 0 < (RefinedUpperRepair.fine n : ℝ) := by
    have h := RefinedUpperParameterCounts.samples_positive hs256 he
    change 0 < (RefinedUpperParameterCounts.samples _ _ : ℝ)
    exact_mod_cast (show 0 < RefinedUpperParameterCounts.samples (scale n) (logarithm (scale n)) by omega)
  have hDpos : 0 < selectedDistance (by omega)
      (UpperGridData.table active origin
        (UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw)) cutter :=
    (div_pos htau (by norm_num)).trans_le hD
  have hp := large_acceptance_probability μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive
    (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw cutter hcap.2 hcap.1 hDpos
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  apply UpperSnapshotProtocol.finish_accepted_mono (by omega) chores active _ _ _ _ _ _ hp
  apply large_margin_scale _ _ _ _ hD htau.le (by positivity) hsample
  exact_mod_cast hcount
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
