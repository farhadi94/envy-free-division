import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishSuccess
import EnvyFreeResearch.Full.UpperGlobalPhysicalRepairTransport

/-! The accepted actual Repair at manuscript parameters discharges every
local transport premise and yields a committed original-population anchor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperCircularStage UpperRepairPreparationChecks GlobalCompletion
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
  [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
  (hvalid : Valid (if chores then .chore else .cake) (p.anchor.table μ))
  (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
  (hnear : UpperRepairPreparationChecks.Near chores μ (enumerate p.anchor.active) p.buffer
    (localEndowments p) (UpperRepair.nearError n))
  (tape : UpperRepair.Tape n p.anchor.active.card)
  (hsuccess : (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
    p.buffer (localEndowments p) tape).2.2 = false)

include hp hpolicy hvalid hpositive hnear hsuccess in
 theorem actual_finish :
    (finish p (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) tape)).Committed μ (if chores then .chore else .cake) whole ∧
    Nonempty (WholeAddition (p.anchor.table μ).value
      ((finish p (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
        p.buffer (localEndowments p) tape)).table μ).value
      (p.anchor.table μ).active (p.anchor.table μ).residue
      ((finish p (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
        p.buffer (localEndowments p) tape)).table μ).residue) := by
  have hold := localEndowments_wf μ whole p hp
  have hpair := localEndowments_pair μ whole p hp
  have hsep := localEndowments_separate μ whole p hp
  have hhist := localEndowments_history p
  have facts := UpperRepair.success_facts μ policy hpolicy hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p) hold hnear
    hpair hsep hhist tape hsuccess
  obtain ⟨f,localAdded,hl,hsub,_hbalance,_hquarter⟩ :=
    UpperGlobalPhysicalRepair.actual_transport μ policy hpolicy hk chores (enumerate p.anchor.active)
      (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p) hold hnear
      hpair hsep hhist tape hsuccess
  exact success_finish μ whole p hp chores hvalid _ facts f localAdded hl hsub

end EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
