import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishSuccess
import EnvyFreeResearch.Full.UpperGlobalPhysicalRepairBalance

/-! The saved strong comparison survives the actual successful final Repair.
The loss is charged to the literal added pieces, whose total is below one
quarter of the buffer. Both signs use the same original observer. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperGlobalPhysicalRepair GlobalCompletion
variable {n : ℕ}

theorem success_strong_margin
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (chores : Bool) (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : UpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result)
    (f : Equiv.Perm (Fin p.anchor.active.card))
    (localAdded : Fin p.anchor.active.card → State n)
    (hl : ∀ j, domain (result.1 (f j)).cells =
      domain (localEndowments p j).cells ∪ domain (localAdded j).cells)
    (hsub : ∀ j, domain (localAdded j).cells ⊆ domain p.buffer.cells)
    (b h : Fin p.anchor.active.card) (tau : ℝ)
    (hstrong : (2-tau) * (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments)
        (enumerate p.anchor.active b) (enumerate p.anchor.active h)) :
    (7/4-tau) * (μ (enumerate p.anchor.active b)).real (domain p.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ (output p result.1))
        (enumerate p.anchor.active b) (enumerate p.anchor.active (f h)) := by
  have hv (j : Fin p.anchor.active.card) :
      (μ (enumerate p.anchor.active b)).real (domain (result.1 (f j)).cells) =
        (μ (enumerate p.anchor.active b)).real (domain (localEndowments p j).cells) +
        (μ (enumerate p.anchor.active b)).real (domain (localAdded j).cells) := by
    rw [hl j]
    exact measureReal_union
      ((localEndowments_separate μ whole p hp j).mono_right (hsub j)) (domain_measurable _)
  have hquarter := success_additions_quarter μ chores (enumerate p.anchor.active)
    p.buffer (localEndowments p) localAdded result facts f hl
    (localEndowments_separate μ whole p hp) hsub b
  have hadd (j : Fin p.anchor.active.card) :
      (μ (enumerate p.anchor.active b)).real (domain (localAdded j).cells) ≤
        ∑ r, (μ (enumerate p.anchor.active b)).real (domain (localAdded r).cells) :=
    Finset.single_le_sum
      (f := fun r => (μ (enumerate p.anchor.active b)).real (domain (localAdded r).cells))
      (fun r _ => measureReal_nonneg) (Finset.mem_univ j)
  have hn (j : Fin p.anchor.active.card) :
      0 ≤ (μ (enumerate p.anchor.active b)).real (domain (localAdded j).cells) :=
    measureReal_nonneg
  have hef := facts.envyFree b (f b)
  have hvb := hv b
  have hvh := hv h
  cases chores <;>
    simp only [Bool.false_eq_true,if_false,if_true,margin,value,output_active,
      localEndowments] at hstrong hef hvb hvh ⊢
  · have hb := hn b
    have hh := (hadd h).trans_lt hquarter
    nlinarith
  · have hh := hn h
    have hb := (hadd b).trans_lt hquarter
    nlinarith

end EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
