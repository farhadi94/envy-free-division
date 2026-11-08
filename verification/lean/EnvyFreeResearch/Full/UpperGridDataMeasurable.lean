import EnvyFreeResearch.Full.UpperGridData

/-! Joint Borel measurability of the pure cached preparation guard. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperGridData

open ProtocolMeasurable UpperDomainDifference UpperCorrectionExecution UpperLogicalPreparation

variable {n coarse fine : ℕ} {Agent : Type*} [Fintype Agent]
  {X : Type*} [MeasurableSpace X]

theorem selectedParents_measurable (active : Agent → Fin n) (origin : X → State n)
    (data : X → Data n coarse fine) (jobs : List (Agent × Agent))
    (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => selectedParents active (origin x) (data x) jobs) := by
  have h := measurable_option_cases (present := fun _ result => result.2)
    (absent := fun _ : X => (∅ : Finset (Fin (coarse + 1))))
    (representatives_measurable active origin data jobs horigin hdata)
    (measurable_snd.comp measurable_snd) measurable_const
  convert h using 1
  funext x
  unfold selectedParents
  cases representatives active (origin x) (data x) jobs <;> rfl

theorem guard_measurable (active : Agent → Fin n) (origin : X → State n)
    (data : X → Data n coarse fine) (jobs : List (Agent × Agent)) (theta : I)
    (cap : X → ℝ) (labels : X → Fin (coarse + 1) → I)
    (horigin : Measurable origin) (hdata : Measurable data) (hcap : Measurable cap)
    (hlabels : ∀ p, Measurable (fun x => labels x p)) :
    Measurable (fun x => guard active (origin x) (data x) jobs theta (cap x) (labels x)) := by
  have hstate := reserve_measurable data theta labels hdata hlabels
  have hindices := reserveCells_measurable (fun x => parent (data x)) theta labels
    (parent_measurable data hdata) hlabels
  have hfinal := selectedParents_measurable active origin data jobs horigin hdata
  have hcount : Measurable (fun x => ((reserveCells (parent (data x)) theta (labels x)).card : ℝ)) :=
    (measurable_of_countable (fun s : Finset (Fin (coarse + fine + 1)) => (s.card : ℝ))).comp hindices
  apply decide_measurable
  have heq : {x : X |
      (∀ a, (theta : ℝ) / 2 * total (origin x) (active a) ≤ total (reserve (data x) theta (labels x)) (active a)) ∧
      ((reserveCells (parent (data x)) theta (labels x)).card : ℝ) ≤ cap x ∧
      ∀ p ∈ selectedParents active (origin x) (data x) jobs, ¬labels x p ≤ theta} =
      (⋂ a, {x : X | (theta : ℝ) / 2 * total (origin x) (active a) ≤
        total (reserve (data x) theta (labels x)) (active a)}) ∩
      ({x : X | ((reserveCells (parent (data x)) theta (labels x)).card : ℝ) ≤ cap x} ∩
        ⋂ p, {x : X | p ∈ selectedParents active (origin x) (data x) jobs → ¬labels x p ≤ theta}) := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  refine (MeasurableSet.iInter (fun a => measurableSet_le
    (measurable_const.mul (total_measurable origin (fun _ => active a) horigin measurable_const))
    (total_measurable _ (fun _ => active a) hstate measurable_const))).inter
      ((measurableSet_le hcount hcap).inter (MeasurableSet.iInter (fun p => ?_)))
  have heq : {x : X | p ∈ selectedParents active (origin x) (data x) jobs → ¬labels x p ≤ theta} =
      ({x : X | p ∈ selectedParents active (origin x) (data x) jobs} ∩ {x : X | labels x p ≤ theta})ᶜ := by
    ext x
    simp only [mem_setOf_eq, mem_compl_iff, mem_inter_iff]
    tauto
  rw [heq]
  exact (((measurableSet_mem_finset p).preimage hfinal).inter
    (measurableSet_le (hlabels p) measurable_const)).compl

end EnvyFreeResearch.Full.UpperGridData
