import EnvyFreeResearch.Full.UpperCorrectionExecution
import EnvyFreeResearch.Full.UpperFreshSamples

/-!
# The actual finite correction loop and its stopping rule

Each proposal is checked using the newly recorded physical payment masses.
At the first failed check, its answers are retained and further proposals
issue no queries. This file proves the program's Borel behavior, one-step
physical check interpretation, and all-outcome finite query accounting.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionLoop

open UpperCircularStage UpperStageMeasurable UpperDomainDifference ProtocolMeasurable
  UpperCorrectionExecution UpperRecordedDomain

abbrev Circle := UpperCircular.Circle

structure Job (n : ℕ) where
  owner : Fin n
  deficit : ℝ
  previous : Fin n → ℝ
  desired : Fin n → ℝ
  tolerance : Fin n → ℝ
  checked : Fin n → Bool

def jobCode {n : ℕ} (job : Job n) : Fin n × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Bool) :=
  (job.owner, job.deficit, job.previous, job.desired, job.tolerance, job.checked)

instance jobMeasurableSpace {n : ℕ} : MeasurableSpace (Job n) :=
  MeasurableSpace.comap jobCode inferInstance

theorem jobCode_measurable {n : ℕ} : Measurable (jobCode (n := n)) := comap_measurable _

theorem job_owner_measurable {n : ℕ} : Measurable (Job.owner (n := n)) :=
  measurable_fst.comp jobCode_measurable

theorem job_deficit_measurable {n : ℕ} : Measurable (Job.deficit (n := n)) :=
  measurable_fst.comp (measurable_snd.comp jobCode_measurable)

theorem job_previous_measurable {n : ℕ} (i : Fin n) : Measurable (fun j : Job n => j.previous i) :=
  (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp jobCode_measurable)))

theorem job_desired_measurable {n : ℕ} (i : Fin n) : Measurable (fun j : Job n => j.desired i) :=
  (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp jobCode_measurable))))

theorem job_tolerance_measurable {n : ℕ} (i : Fin n) : Measurable (fun j : Job n => j.tolerance i) :=
  (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp jobCode_measurable)))))

theorem job_checked_measurable {n : ℕ} (i : Fin n) : Measurable (fun j : Job n => j.checked i) :=
  (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp jobCode_measurable)))))

def Acceptable {n : ℕ} (job : Job n) (before after : State n) : Prop :=
  ∀ i, job.checked i = true →
    |job.previous i + observedPayment before after i - job.desired i| ≤ job.tolerance i

def accepts {n : ℕ} (job : Job n) (before after : State n) : Bool := decide (Acceptable job before after)

structure LoopState (n : ℕ) where
  current : State n
  stopped : Bool
  accepted : List Correction

def loopCode {n : ℕ} (state : LoopState n) : State n × Bool × List Correction :=
  (state.current, state.stopped, state.accepted)

instance loopMeasurableSpace {n : ℕ} : MeasurableSpace (LoopState n) :=
  MeasurableSpace.comap loopCode inferInstance

theorem loopCode_measurable {n : ℕ} : Measurable (loopCode (n := n)) := comap_measurable _

theorem loop_current_measurable {n : ℕ} : Measurable (LoopState.current (n := n)) :=
  measurable_fst.comp loopCode_measurable

theorem loop_stopped_measurable {n : ℕ} : Measurable (LoopState.stopped (n := n)) :=
  measurable_fst.comp (measurable_snd.comp loopCode_measurable)

theorem loop_accepted_measurable {n : ℕ} : Measurable (LoopState.accepted (n := n)) :=
  measurable_snd.comp (measurable_snd.comp loopCode_measurable)

def initial {n : ℕ} (state : State n) : LoopState n := ⟨state, false, []⟩

/-- The Boolean output marks the first rejecting correction only. -/
def step {n : ℕ} (policy : Policy n) (state : LoopState n) (draw : Job n × Circle) : Bool × LoopState n :=
  if state.stopped then (false, state) else
  let next := execute policy state.current draw.1.owner draw.1.deficit draw.2
  if accepts draw.1 state.current next.2 then
    (false, ⟨next.2, false, state.accepted ++ [next.1]⟩)
  else
    (true, ⟨⟨state.current.cells, next.2.history⟩, true, state.accepted⟩)

def run {n m : ℕ} (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) : (Fin m → Bool) × LoopState n :=
  UpperFreshSamples.run (step policy) m state (fun i => (jobs i, tape i))

variable {n : ℕ}

theorem step_query_bound (policy : Policy n) (state : LoopState n) (draw : Job n × Circle) :
    (step policy state draw).2.current.history.length ≤ state.current.history.length + 2 * (n + 1) := by
  unfold step
  split_ifs
  · change state.current.history.length ≤ _
    omega
  · dsimp only
    split_ifs <;> exact query_bound policy state.current draw.1.owner draw.1.deficit draw.2

theorem step_cut_bound (policy : Policy n) (state : LoopState n) (draw : Job n × Circle) :
    ((step policy state draw).2.current.history.map Prod.fst).countP isCut ≤
      (state.current.history.map Prod.fst).countP isCut + 2 := by
  unfold step
  split_ifs
  · change (state.current.history.map Prod.fst).countP isCut ≤ _
    omega
  · dsimp only
    split_ifs <;> exact cut_bound policy state.current draw.1.owner draw.1.deficit draw.2

/-- This cap includes every rejecting correction and every tape, rather than
only the successful trajectories. -/
theorem run_query_bound {m : ℕ} (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) :
    (run policy jobs state tape).2.current.history.length ≤
      state.current.history.length + m * (2 * (n + 1)) :=
  UpperFreshSamples.cost_bound (step policy) (fun s => s.current.history.length) (2 * (n + 1))
    (step_query_bound policy) m state _

theorem run_cut_bound {m : ℕ} (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) :
    ((run policy jobs state tape).2.current.history.map Prod.fst).countP isCut ≤
      (state.current.history.map Prod.fst).countP isCut + m * 2 :=
  UpperFreshSamples.cost_bound (step policy)
    (fun s => (s.current.history.map Prod.fst).countP isCut) 2
    (step_cut_bound policy) m state _

theorem step_stopped (policy : Policy n) (state : LoopState n) (draw : Job n × Circle)
    (h : state.stopped = true) : step policy state draw = (false, state) := by simp [step, h]

theorem step_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (state : LoopState n) (hstate : WellFormed μ state.current) (draw : Job n × Circle)
    (hpositive : state.stopped = false → 0 < (μ draw.1.owner).real (domain state.current.cells)) :
    WellFormed μ (step policy state draw).2.current := by
  by_cases hs : state.stopped = true
  · rw [step_stopped policy state draw hs]
    exact hstate
  · have hf : state.stopped = false := Bool.eq_false_iff.mpr hs
    have hp := hpositive hf
    simp only [step, hf, Bool.false_eq_true, ite_false]
    split_ifs
    · exact execute_wellFormed μ policy hpolicy state.current hstate draw.1.owner hp draw.1.deficit draw.2
    · exact rejected_wellFormed μ policy hpolicy state.current hstate draw.1.owner hp draw.1.deficit draw.2

/-- The actual cached acceptance test is precisely the physical payment
inequality for every original observer. -/
theorem accepts_physical_iff (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (job : Job n)
    (hpositive : 0 < (μ job.owner).real (domain state.cells)) (start : Circle) :
    accepts job state (execute policy state job.owner job.deficit start).2 = true ↔
      ∀ i, job.checked i = true →
        |job.previous i + (μ i).real (payment policy state job.owner job.deficit start) - job.desired i| ≤
        job.tolerance i := by
  simp only [accepts, Acceptable]
  simp only [observedPayment_correct μ policy hpolicy state hstate job.owner hpositive job.deficit start]
  simp

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem accepts_measurable (job : X → Job n) (before after : X → State n)
    (hjob : Measurable job) (hbefore : Measurable before) (hafter : Measurable after) :
    Measurable (fun z => accepts (job z) (before z) (after z)) := by
  apply decide_measurable
  have hset : {z | Acceptable (job z) (before z) (after z)} =
      ⋂ i, ({z | (job z).checked i ≠ true} ∪
        {z | |(job z).previous i + observedPayment (before z) (after z) i - (job z).desired i| ≤
          (job z).tolerance i}) := by
    ext z
    simp only [Acceptable, mem_ofPred_eq, mem_iInter, mem_union]
    exact forall_congr' (fun _ => imp_iff_not_or)
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply (measurableSet_eq_fun ((job_checked_measurable i).comp hjob) measurable_const).compl.union
  exact measurableSet_le
    (((job_previous_measurable i).comp hjob).add
      (observedPayment_measurable before after (fun _ => i) hbefore hafter measurable_const) |>.sub
      ((job_desired_measurable i).comp hjob) |>.abs)
    ((job_tolerance_measurable i).comp hjob)

theorem loop_mk_measurable (current : X → State n) (stopped : X → Bool) (accepted : X → List Correction)
    (hc : Measurable current) (hs : Measurable stopped) (ha : Measurable accepted) :
    Measurable (fun z => (⟨current z, stopped z, accepted z⟩ : LoopState n)) :=
  measurable_comap_iff.mpr (hc.prodMk (hs.prodMk ha))

theorem step_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy) :
    Measurable (Function.uncurry (step policy)) := by
  classical
  let X := LoopState n × (Job n × Circle)
  have hcurrent : Measurable (fun p : X => p.1.current) := loop_current_measurable.comp measurable_fst
  have hjob : Measurable (fun p : X => p.2.1) := measurable_fst.comp measurable_snd
  have hnext : Measurable (fun p : X => execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2) :=
    execute_measurable policy hpolicy _ _ _ _ hcurrent (job_owner_measurable.comp hjob)
      (job_deficit_measurable.comp hjob) (measurable_snd.comp measurable_snd)
  have haccept := accepts_measurable _ _ _ hjob hcurrent (measurable_snd.comp hnext)
  have haccepted : Measurable (fun p : X => p.1.accepted) := loop_accepted_measurable.comp measurable_fst
  have hcommit : Measurable (fun p : X =>
      (false, (⟨(execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2).2, false,
        p.1.accepted ++ [(execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2).1]⟩ : LoopState n))) :=
    measurable_const.prodMk (loop_mk_measurable _ _ _ (measurable_snd.comp hnext) measurable_const
      (measurable_list_append.comp (haccepted.prodMk
        (measurable_list_singleton.comp (measurable_fst.comp hnext)))))
  have hrestore : Measurable (fun p : X =>
      (⟨p.1.current.cells, (execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2).2.history⟩ : State n)) :=
    by
      apply measurable_comap_iff.mpr
      change Measurable (fun p : X => (p.1.current.cells,
        (execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2).2.history))
      exact (state_cells_measurable.comp hcurrent).prodMk
        (state_history_measurable.comp (measurable_snd.comp hnext))
  have habort : Measurable (fun p : X =>
      (true, (⟨⟨p.1.current.cells, (execute policy p.1.current p.2.1.owner p.2.1.deficit p.2.2).2.history⟩,
        true, p.1.accepted⟩ : LoopState n))) :=
    measurable_const.prodMk (loop_mk_measurable _ _ _ hrestore measurable_const haccepted)
  exact (measurable_const.prodMk measurable_fst).ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp measurable_fst) measurable_const)
    (hcommit.ite (measurableSet_eq_fun haccept measurable_const) habort)

theorem run_measurable {m : ℕ} (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : Fin m → Job n) :
    Measurable (fun p : LoopState n × (Fin m → Circle) => run policy jobs p.1 p.2) := by
  have ht : Measurable (fun p : LoopState n × (Fin m → Circle) => fun i => (jobs i, p.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)
  exact (UpperFreshSamples.run_measurable (step policy) (step_measurable policy hpolicy) m).comp
    (measurable_fst.prodMk ht)

end Measurability

end EnvyFreeResearch.Full.UpperCorrectionLoop
