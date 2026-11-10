import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinishWitnessFacts

/-! The actual accepted Repair extends the common enclosing history; frozen
bundles keep their earlier truthful caches, now included in that history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperCircularStage UpperRepairPreparationChecks
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
include hp
 theorem success_finish_history (chores : Bool)
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : RefinedUpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result)
    (hext : p.buffer.history ⊆ result.2.1.history) : (finish p result).HistoryCompatible := by
  intro j
  change (output p result.1 j).history ⊆ result.2.1.history
  by_cases hj : j ∈ p.anchor.active
  · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
    rw [output_active,facts.common_history]
  · rw [output_frozen _ _ _ hj]
    intro qr hqr
    exact hext (hp.old_history j hqr)

variable [Nonempty (Fin p.anchor.active.card)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
  (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
  (hnear : Near chores μ (enumerate p.anchor.active) p.buffer (localEndowments p) (RefinedUpperRepair.nearError n))
  (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
  (hsuccess : (RefinedUpperRepair.execute policy hk chores (enumerate p.anchor.active)
    p.buffer (localEndowments p) tape).2.2 = false)
include hp hpolicy hpositive hnear hsuccess in
 theorem actual_finish_history : (finish p (RefinedUpperRepair.execute policy hk chores
    (enumerate p.anchor.active) p.buffer (localEndowments p) tape)).HistoryCompatible := by
  have facts := RefinedUpperRepair.success_facts μ policy hpolicy hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p)
    (localEndowments_wf μ whole p hp) hnear
    (localEndowments_pair μ whole p hp) (localEndowments_separate μ whole p hp)
    (localEndowments_history p) tape hsuccess
  obtain ⟨trace,_hex,hh,_hQ,_hC⟩ := RefinedUpperRepair.program_cost policy hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer (localEndowments p) tape
  apply success_finish_history μ whole p hp chores _ facts
  rw [hh]
  exact List.subset_append_left _ _

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
