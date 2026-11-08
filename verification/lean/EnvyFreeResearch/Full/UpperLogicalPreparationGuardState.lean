import EnvyFreeResearch.Full.UpperLogicalPreparation

/-!
# Actual Borel preparation guard on the original sampler and label tapes

The guard reads only cached raw totals, the retained logical-cell index set,
and the actual final representative-parent set. Parent labels remain fresh
and independent of the full fine-sampler history.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparationGuard

open UpperLogicalPreparation UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperStageMeasurable UpperRecordedQuantiles UpperDomainDifference UpperGridCells UpperLogicalCells Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

def selectedParents (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent)) : Finset (Fin (count (Agent := Agent) q + 1)) :=
  match representativeRun policy active origin q m draw jobs with
  | none => ∅
  | some result => result.2

def Passes (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) : Prop :=
  (∀ a, (theta : ℝ) / 2 * total origin (active a) ≤
    total (reserveState policy active origin q m draw theta labels) (active a)) ∧
  ((reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels).card : ℝ) ≤ cap ∧
  ∀ p ∈ selectedParents policy active origin q m draw jobs, ¬labels p ≤ theta

def guard (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) : Bool :=
  decide (Passes policy active origin q m jobs theta cap draw labels)

theorem guard_eq_true (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (draw : Fin m → Agent × I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    guard policy active origin q m jobs theta cap draw labels = true ↔
      Passes policy active origin q m jobs theta cap draw labels := by
  exact decide_eq_true_iff

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem selectedParents_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) (jobs : List (Agent × Agent)) :
    Measurable (fun p : State n × (Fin m → Agent × I) => selectedParents policy active p.1 q m p.2 jobs) := by
  have h := ProtocolMeasurable.measurable_option_cases
    (present := fun (_ : State n × (Fin m → Agent × I))
      (result : List (Fin (count (Agent := Agent) q + m + 1) × Fin (count (Agent := Agent) q + m + 1)) ×
        Finset (Fin (count (Agent := Agent) q + 1))) => result.2)
    (absent := fun _ => (∅ : Finset (Fin (count (Agent := Agent) q + 1))))
    (representativeRun_measurable policy hpolicy active q m jobs)
    (measurable_snd.comp measurable_snd) measurable_const
  convert h using 1
  funext p
  unfold selectedParents
  cases representativeRun policy active p.1 q m p.2 jobs <;> rfl

theorem fixed_origin_measurable {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (f : (A × B) × C → D) (hf : Measurable f) (a : A) :
    Measurable (fun p : B × C => f ((a, p.1), p.2)) :=
  hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

theorem fixed_origin_projection_measurable {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (f : A × B → D) (hf : Measurable f) (a : A) :
    Measurable (fun p : B × C => f (a, p.1)) :=
  hf.comp (measurable_const.prodMk measurable_fst)

set_option maxHeartbeats 800000 in
theorem passes_measurableSet (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ) :
    MeasurableSet {p : (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I) |
      Passes policy active origin q m jobs theta cap p.1 p.2} := by
  let X := (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I)
  have hstate : Measurable (fun p : X => reserveState policy active origin q m p.1 theta p.2) :=
    fixed_origin_measurable
      (fun p : (State n × (Fin m → Agent × I)) × (Fin (count (Agent := Agent) q + 1) → I) =>
        reserveState policy active p.1.1 q m p.1.2 theta p.2)
      (reserveState_measurable policy hpolicy active q m theta) origin
  have hparent (e : Fin (count (Agent := Agent) q + m + 1)) :
      Measurable (fun p : X => UpperRecordedParents.parent policy active origin q m p.1 e) :=
    fixed_origin_projection_measurable
      (fun p : State n × (Fin m → Agent × I) => UpperRecordedParents.parent policy active p.1 q m p.2 e)
      (UpperRecordedParents.parent_measurable policy hpolicy active q m e) origin
  have hindices : Measurable (fun p : X => reserveCells
      (UpperRecordedParents.parent policy active origin q m p.1) theta p.2) :=
    reserveCells_measurable _ theta _ hparent (fun c => (measurable_pi_apply c).comp measurable_snd)
  have hfinal : Measurable (fun p : X => selectedParents policy active origin q m p.1 jobs) :=
    fixed_origin_projection_measurable
      (fun p : State n × (Fin m → Agent × I) => selectedParents policy active p.1 q m p.2 jobs)
      (selectedParents_measurable policy hpolicy active q m jobs) origin
  have hcount : Measurable (fun p : X =>
      ((reserveCells (UpperRecordedParents.parent policy active origin q m p.1) theta p.2).card : ℝ)) :=
    (measurable_of_countable (fun s : Finset (Fin (count (Agent := Agent) q + m + 1)) => (s.card : ℝ))).comp hindices
  have heq : {p : X | Passes policy active origin q m jobs theta cap p.1 p.2} =
    ((⋂ a, {p : X | (theta : ℝ) / 2 * total origin (active a) ≤
    total (reserveState policy active origin q m p.1 theta p.2) (active a)}) ∩
    ({p : X | ((reserveCells (UpperRecordedParents.parent policy active origin q m p.1) theta p.2).card : ℝ) ≤ cap} ∩
      ⋂ c, {p : X | c ∈ selectedParents policy active origin q m p.1 jobs → ¬p.2 c ≤ theta})) := by
    ext p
    simp only [Passes, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [heq]
  refine (MeasurableSet.iInter (fun a => measurableSet_le measurable_const
    (total_measurable _ (fun _ => active a) hstate measurable_const))).inter
      ((measurableSet_le hcount measurable_const).inter (MeasurableSet.iInter (fun c => ?_)))
  have heq : {p : X | c ∈ selectedParents policy active origin q m p.1 jobs → ¬p.2 c ≤ theta} =
      ({p : X | c ∈ selectedParents policy active origin q m p.1 jobs} ∩ {p : X | p.2 c ≤ theta})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff]
    tauto
  rw [heq]
  exact (((measurableSet_mem_finset c).preimage hfinal).inter
    (measurableSet_le ((measurable_pi_apply c).comp measurable_snd) measurable_const)).compl

theorem guard_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (origin : State n) (q m : ℕ) (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ) :
    Measurable (fun p : (Fin m → Agent × I) × (Fin (count (Agent := Agent) q + 1) → I) =>
      guard policy active origin q m jobs theta cap p.1 p.2) :=
  decide_measurable _ (passes_measurableSet policy hpolicy active origin q m jobs theta cap)

end Measurability

end EnvyFreeResearch.Full.UpperLogicalPreparationGuard
