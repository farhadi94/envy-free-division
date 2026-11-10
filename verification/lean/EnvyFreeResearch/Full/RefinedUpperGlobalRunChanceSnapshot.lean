import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunChancePrefix
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolProbability

/-! The completed actual Snapshot probability theorem supplies the remaining
valid-phase success law under the universal fresh draw. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperZeroRows RefinedUpperGlobalTape RefinedUpperGlobalRunChance
variable {n : ℕ}

theorem snapshot_universal_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (a : Anchor n)
    (ha : RefinedUpperGlobalNormalize.Normalized μ chores whole (.snapshot a))
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (4 : ℝ≥0∞) * universalLaw n {draw | Phase.accepted policy chores (.snapshot a) draw=true} := by
  have hk : 3 ≤ a.active.card := ha.2.2.1
  letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
  have hpositive : ∀ i, 0 < (μ (enumerate a.active i)).real (domain a.residue.cells) := by
    intro i
    rw [← total_correct μ a.residue ha.1.1.residue_wellFormed]
    exact ha.2.2.2.1 _ (enumerate_mem _ i)
  have hprob := RefinedUpperSnapshotProtocol.snapshot_acceptance_probability μ policy hpolicy hmeas hk
    chores (enumerate a.active) (enumerate_injective _) a.residue ha.1.1.residue_wellFormed
    hpositive ⟨0,by omega⟩
  have hr : Measurable (fun tape => (a.snapshotResult policy hk chores tape).2.2) := by
    exact measurable_snd.comp (measurable_snd.comp
      (RefinedUpperSnapshotProtocol.snapshotExecute_measurable policy hmeas hk chores (enumerate a.active)
        (fun _ : RefinedUpperSnapshotProtocol.Tape n a.active.card => a.residue) ⟨0,by omega⟩ id
        measurable_const measurable_id))
  have hf : 1 ≤ (4 : ℝ≥0∞) * RefinedUpperSnapshotProtocol.law n a.active.card
      {tape | (a.snapshotResult policy hk chores tape).2.2=false} := by
    apply (ENNReal.toReal_le_toReal (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))).mp
    norm_num [ENNReal.toReal_mul]
    change 1/4 < (RefinedUpperSnapshotProtocol.law n a.active.card
      {tape | (a.snapshotResult policy hk chores tape).2.2=false}).toReal at hprob
    linarith
  have he : {draw | Phase.accepted policy chores (.snapshot a) draw=true} =
      {draw : Universal n | (a.snapshotResult policy hk chores
        (draw (a.request (by omega) .snapshot))).2.2=false} := by
    ext draw
    simp only [Phase.accepted,dite_eq_left hk,Bool.not_eq_true']
  rw [he,request_false_probability (a.request (by omega) .snapshot) _ hr]
  exact hf

theorem valid_snapshot_phase_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (phase : Phase n) (hv : phase.Valid μ chores whole) (hkind : phase.paidKind=some .snapshot)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (4 : ℝ≥0∞) * universalLaw n {draw | Phase.accepted policy chores phase draw=true} := by
  cases phase with
  | normalize a => simp [Phase.paidKind] at hkind
  | snapshot a => exact snapshot_universal_factor μ whole chores a hv policy hpolicy hmeas
  | firstShrink p G => simp [Phase.paidKind] at hkind
  | secondShrink p => simp [Phase.paidKind] at hkind
  | finalRepair p => simp [Phase.paidKind] at hkind
  | done a => simp [Phase.paidKind] at hkind

theorem snapshot_original_attempt_bound (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (fallback : Fin n)
    (hstep : Measurable (Function.uncurry (Phase.step policy fallback chores)))
    (haccept : Measurable (Function.uncurry (Phase.accepted policy chores))) (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .snapshot t) ≤
      (4 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .snapshot t) := by
  apply finitePrefix_attempt_bound policy fallback chores hstep haccept initial .snapshot t _ (by finiteness)
  intro pastDraws hp
  exact valid_snapshot_phase_factor μ whole chores _
    (finiteRun_valid μ whole chores initial hinit policy hpolicy fallback t pastDraws) hp policy hpolicy hmeas

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
