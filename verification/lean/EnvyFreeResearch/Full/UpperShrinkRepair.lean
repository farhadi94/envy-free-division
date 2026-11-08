import EnvyFreeResearch.Full.UpperShrinkCarved

/-! The actual fresh Repair following a carved domain. Carving validity is
an explicit intermediate obligation until the deterministic carve executor
is connected; this module does not claim a complete Shrink protocol. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (G : ℝ) (hG : 0 < G) (out : Carved n k)
  (valid : out.Valid μ active origin G (UpperRepair.nearError n))
  (htau : 0 ≤ UpperRepair.nearError n)
  (hktau : (k : ℝ) * UpperRepair.nearError n ≤ 2)

include hpositive hG valid htau hktau hk in
theorem repair_buffer_positive (i : Fin k) :
    0 < (μ (active i)).real (domain out.buffer.cells) :=
  carving_positive (hpositive i) hG
    (carved_buffer_bounds μ active origin G _ out valid (by omega) hG htau hktau i).1

include hpolicy hpositive hG valid htau hktau hinj in
theorem repaired_facts (p : UpperRepair.Tape n k)
    (haccept : (UpperRepair.execute policy hk chores active out.buffer out.old p).2.2 = false) :
    SuccessFacts μ chores active out.buffer out.old
      (UpperRepair.execute policy hk chores active out.buffer out.old p) ∧
    ((⋃ j, domain ((UpperRepair.execute policy hk chores active out.buffer out.old p).1 j).cells) ∪
      domain (UpperRepair.execute policy hk chores active out.buffer out.old p).2.1.cells = domain origin.cells) ∧
    (∀ i, 3 * (μ (active i)).real (domain origin.cells) / (8 * G) ≤
      (μ (active i)).real (domain (UpperRepair.execute policy hk chores active out.buffer out.old p).2.1.cells) ∧
      (μ (active i)).real (domain (UpperRepair.execute policy hk chores active out.buffer out.old p).2.1.cells) ≤
        (μ (active i)).real (domain origin.cells) / G) := by
  have hp := repair_buffer_positive μ hk active origin hpositive G hG out valid htau hktau
  have hn := carved_near μ active origin G _ out valid (by omega) hG htau hktau chores
  have hs := UpperRepair.success_facts μ policy hpolicy hk chores active hinj out.buffer
    valid.buffer_wellFormed hp out.old valid.old_wellFormed hn valid.old_disjoint valid.old_buffer
    (fun j => by rw [valid.common_history j]) p haccept
  refine ⟨hs, hs.material_preserved.trans valid.material, fun i => ?_⟩
  exact repaired_residue_bounds hG
    (carved_buffer_bounds μ active origin G _ out valid (by omega) hG htau hktau i)
    (hs.residue_mass i)

include hpolicy hpositive hG valid htau hktau hinj in
theorem repair_failure_lt (hmeas : MeasurablePolicy policy) :
    UpperRepair.law n k {p | (UpperRepair.execute policy hk chores active out.buffer out.old p).2.2 = true} < 1 / 64 := by
  have hp := repair_buffer_positive μ hk active origin hpositive G hG out valid htau hktau
  exact UpperRepair.failure_lt μ policy hpolicy hk chores active hinj out.buffer valid.buffer_wellFormed hp
    out.old valid.old_wellFormed (carved_near μ active origin G _ out valid (by omega) hG htau hktau chores) hmeas

end EnvyFreeResearch.Full.UpperShrink
