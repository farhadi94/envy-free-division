import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolProgressLocal
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinishWitness
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolState

/-! A successful physical continuation creates a new dominated target while
transporting all previous targets by its actual whole-bundle permutation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open GlobalCompletion
variable {n : ℕ}

theorem success_potential_growth
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (chores : Bool) (hvalid : Valid (if chores then .chore else .cake) (p.anchor.table μ))
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : RefinedUpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result)
    (w : Witness μ p result) (b h : Fin p.anchor.active.card)
    (tau : ℝ) (htau : tau ≤ 1/2)
    (hpositive : 0 < (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells))
    (hedge : p.anchor.edge (if chores then .chore else .cake)
      (enumerate p.anchor.active b) (enumerate p.anchor.active h))
    (hstrong : (2-tau) * (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments)
        (enumerate p.anchor.active b) (enumerate p.anchor.active h)) :
    statePotential (if chores then .chore else .cake) (p.anchor.table μ) + 1 ≤
      statePotential (if chores then .chore else .cake) ((finish p result).table μ) := by
  have hc := (success_finish μ whole p hp chores hvalid result facts
    w.receiver w.addition w.label w.subset_buffer).1
  have hm := success_strong_margin μ whole p hp chores result facts
    w.receiver w.addition w.label w.subset_buffer b h tau hstrong
  have hr := facts.residue_mass b
  have hpos : 0 < ((finish p result).table μ).residue (enumerate p.anchor.active b) := by
    change 0 < (μ (enumerate p.anchor.active b)).real (domain result.2.1.cells)
    nlinarith [hr.1]
  have hw : ((finish p result).table μ).residue (enumerate p.anchor.active b) ≤
      margin (if chores then .chore else .cake) ((finish p result).table μ).value
        (enumerate p.anchor.active b) (w.whole.permutation (enumerate p.anchor.active h)) := by
    rw [w.receiver_eq,extendPermutation_apply]
    change (μ (enumerate p.anchor.active b)).real (domain result.2.1.cells) ≤ _
    change (7/4-tau) * (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) ((finish p result).table μ).value
        (enumerate p.anchor.active b) (enumerate p.anchor.active (w.receiver h)) at hm
    nlinarith [hr.2]
  apply R4GlobalPotential.strict_global_progress
    (margin (if chores then .chore else .cake) (p.anchor.table μ).value)
    (margin (if chores then .chore else .cake) ((finish p result).table μ).value)
    (p.anchor.table μ).residue ((finish p result).table μ).residue w.whole.permutation
    hc.2.2.2.1 (margin_self _ _) hc.2.2.1
  · intro i _ j hj
    have ht : j ≠ i ∧ (p.anchor.table μ).residue i ≤
        margin (if chores then .chore else .cake) (p.anchor.table μ).value i j := by
      simpa [R4GlobalPotential.targets] using hj
    exact whole_addition_domination_transport _ w.whole
      (success_activeEF μ p chores result facts) i j ht.2
  · exact hpos
  · exact edge_missing μ whole p.anchor hp.anchor _ hedge
  · exact hw

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
