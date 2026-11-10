import EnvyFreeResearch.Full.RefinedUpperPreparationProgram
import EnvyFreeResearch.Full.UpperLogicalIsolation

/-! Actual ideal targets and the finite cycle-rejection branch for the new
preparation. Both depend only on returned cached data. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRepairTargets
open UpperIdealPayments UpperLogicalIsolation RefinedUpperPreparationProgram
variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

/-- A is recomputed from the actual retained cache; V is the exact physical
old-plus-seed matrix returned by preparation. -/
def disagreement (active : Fin k → Fin n) (p : Prepared n k coarse fine) : Fin k → Fin k → ℝ :=
  UpperPayments.cellGap (UpperCorrectionSetup.table active p.2.1 (UpperGridData.cuts p.1))

def targets (chores : Bool) (active : Fin k → Fin n) (p : Prepared n k coarse fine)
    (eta lam : ℝ) : Fin k → ℝ :=
  if chores then choreTargets p.2.2.2.1 (disagreement active p) lam eta
  else cakeTargets p.2.2.2.1 (disagreement active p) lam

def approved (chores : Bool) (active : Fin k → Fin n) (p : Prepared n k coarse fine) (lam : ℝ) : Bool :=
  !(cycleReject chores p.2.2.2.1 (disagreement active p) lam)

variable {X : Type} [MeasurableSpace X]

theorem disagreement_measurable (active : Fin k → Fin n) (p : X → Prepared n k coarse fine)
    (hp : Measurable p) (i j : Fin k) : Measurable (fun x => disagreement active (p x) i j) :=
  UpperPayments.cellGap_measurable _ (UpperCorrectionSetup.table_measurable active _ _
    (measurable_fst.comp (measurable_snd.comp hp))
    (fun e => (measurable_pi_apply e).comp (UpperGridData.cuts_measurable _ (measurable_fst.comp hp)))) i j

theorem targets_measurable (chores : Bool) (active : Fin k → Fin n)
    (p : X → Prepared n k coarse fine) (eta lam : ℝ) (hp : Measurable p) (i : Fin k) :
    Measurable (fun x => targets chores active (p x) eta lam i) := by
  have hV (i j : Fin k) : Measurable (fun x => (p x).2.2.2.1 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hp)))))
  cases chores
  · exact UpperIdealMeasurable.cakeTargets_measurable _ _ _ hV (disagreement_measurable active p hp) measurable_const i
  · exact UpperIdealMeasurable.choreTargets_measurable _ _ _ _ hV (disagreement_measurable active p hp)
      measurable_const measurable_const i

theorem approved_measurable (chores : Bool) (active : Fin k → Fin n)
    (p : X → Prepared n k coarse fine) (lam : ℝ) (hp : Measurable p) :
    Measurable (fun x => approved chores active (p x) lam) := by
  apply (measurable_of_countable Bool.not).comp
  apply cycleReject_measurable
  · intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hp)))))
  · exact disagreement_measurable active p hp

end EnvyFreeResearch.Full.RefinedUpperRepairTargets
