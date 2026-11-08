import EnvyFreeResearch.Full.UpperSnapshotIntegrationLarge

/-! The actual large branch meets the manuscript's common Snapshot threshold
at the original population scales. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
  UpperSnapshotCandidates UpperRepairSnapshot UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

def margin (n : ℕ) : ℝ := UpperRepair.nearError n / (768 * UpperRepair.fine n)

theorem finish_accepted_mono (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (lo hi : ℝ) (hle : lo ≤ hi) (origin : State n) (old : Fin k → State n)
    (result : PhysicalResult n k)
    (hs : (finish hk chores active hi origin old result).2.2 = false) :
    (finish hk chores active lo origin old result).2.2 = false := by
  have hp := (passes_iff _ _ _ _ _).mp ((finish_accepted _ _ _ _ _ _ _).mp hs)
  exact (finish_accepted _ _ _ _ _ _ _).mpr ((passes_iff _ _ _ _ _).mpr
    ⟨hp.1,hp.2.1,hle.trans hp.2.2⟩)

theorem configured_large_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (draw : Fin (UpperRepair.fine n) → Fin k × I) (cutter : Fin k)
    (hD : UpperRepair.nearError n /16 ≤ selectedDistance (by omega)
      (UpperGridData.table active origin
        (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw)) cutter) :
    let data := UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw
    let old := candidateOld (by omega) active origin data cutter
    let buffer := candidateBuffer (by omega) active origin data cutter
    31/64 < (UpperRepair.law n k).real
      {p | (execute policy (by omega) chores active (margin n) buffer old p).2.2 = false} := by
  have hs := scale_large n
  have hell : (1:ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have htau : 0 < UpperRepair.nearError n := oldError_positive hs hell
  have hcap := coarse_cap_small hs hell
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hcount := original_scale_cell_count hs hell (active_scale n k hkn) (by omega : 0<k)
  have hsample : 0 < (UpperRepair.fine n : ℝ) := by
    have h := samples_positive hs hell
    exact_mod_cast h
  have hDpos : 0 < selectedDistance (by omega)
      (UpperGridData.table active origin
        (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw)) cutter :=
    (div_pos htau (by norm_num)).trans_le hD
  have hp := large_acceptance_probability μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive
    (UpperRepair.coarse n) (UpperRepair.fine n) draw cutter hcap.2 hcap.1 hDpos
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  apply finish_accepted_mono (by omega) chores active _ _ _ _ _ _ hp
  apply large_margin_scale _ _ _ _ hD htau.le (by positivity) hsample
  exact_mod_cast hcount
end EnvyFreeResearch.Full.UpperSnapshotProtocol
