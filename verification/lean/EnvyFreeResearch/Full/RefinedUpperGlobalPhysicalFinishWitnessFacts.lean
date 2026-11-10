import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinishWitness

/-! Numerical identities read from the actual literal final-Repair witness;
individual spending is derived from its strict aggregate quarter bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
  (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) (w : Witness μ p result)
include hp
 theorem Witness.label_value (i : Fin n) (j : Fin p.anchor.active.card) :
    (μ i).real (domain (result.1 (w.receiver j)).cells) =
      (μ i).real (domain (localEndowments p j).cells) +
      (μ i).real (domain (w.addition j).cells) := by
  rw [w.label]
  exact measureReal_union ((localEndowments_separate μ whole p hp j).mono_right (w.subset_buffer j))
    (domain_measurable _)

 theorem Witness.output_value (i : Fin n) (j : Fin p.anchor.active.card) :
    ((finish p result).table μ).value i (enumerate p.anchor.active (w.receiver j)) =
      (μ i).real (domain (localEndowments p j).cells) +
      (μ i).real (domain (w.addition j).cells) := by
  change (μ i).real (domain (output p result.1 (enumerate p.anchor.active (w.receiver j))).cells) = _
  rw [output_active]
  exact w.label_value μ whole p hp result i j

omit hp
 theorem Witness.individual_quarter (i j : Fin p.anchor.active.card) :
    (μ (enumerate p.anchor.active i)).real (domain (w.addition j).cells) <
      (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells) / 4 := by
  apply lt_of_le_of_lt _ (w.quarter i)
  exact Finset.single_le_sum
    (f := fun a => (μ (enumerate p.anchor.active i)).real (domain (w.addition a).cells))
    (fun a _ => measureReal_nonneg) (Finset.mem_univ j)

 theorem Witness.permutation_active (j : Fin p.anchor.active.card) :
    w.whole.permutation (enumerate p.anchor.active j) = enumerate p.anchor.active (w.receiver j) := by
  rw [w.receiver_eq,extendPermutation_apply]

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
