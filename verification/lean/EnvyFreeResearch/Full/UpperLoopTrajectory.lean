import EnvyFreeResearch.Full.UpperCorrectionTrace
import EnvyFreeResearch.Full.UpperAggregateInterpolationStream

/-! The complete actual finite trajectory, including the state after the
last attempted correction. Pathwise induction refers only to the original
tape coordinates, so recorded endpoints retain their actual provenance. -/

noncomputable section

namespace EnvyFreeResearch.Full.UpperLoopTrajectory

open UpperAggregateInterpolation UpperCorrectionLoop UpperCircularStage

variable {State Draw : Type*}

def trajectory : {r : ℕ} → (Fin r → State → Draw → State) → State →
    (Fin r → Draw) → Fin (r + 1) → State
  | 0, _, initial, _ => fun _ => initial
  | r + 1, step, initial, tape =>
      Fin.cons initial (trajectory (fun i => step i.succ) (step 0 initial (tape 0)) (fun i => tape i.succ))

theorem trajectory_zero {r : ℕ} (step : Fin r → State → Draw → State)
    (initial : State) (tape : Fin r → Draw) : trajectory step initial tape 0 = initial := by
  cases r <;> rfl

theorem trajectory_castSucc {r : ℕ} (step : Fin r → State → Draw → State)
    (initial : State) (tape : Fin r → Draw) (i : Fin r) :
    trajectory step initial tape i.castSucc = reached step initial tape i := by
  induction r generalizing initial with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [trajectory, reached, Fin.castSucc_succ, Fin.cons_succ] using
        ih (fun i => step i.succ) (step 0 initial (tape 0)) (fun i => tape i.succ) j

theorem trajectory_succ {r : ℕ} (step : Fin r → State → Draw → State)
    (initial : State) (tape : Fin r → Draw) (i : Fin r) :
    trajectory step initial tape i.succ = step i (trajectory step initial tape i.castSucc) (tape i) := by
  induction r generalizing initial with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [trajectory, Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero, trajectory_zero]
    · simpa only [trajectory, Fin.castSucc_succ, Fin.cons_succ] using
        ih (fun i => step i.succ) (step 0 initial (tape 0)) (fun i => tape i.succ) j

theorem trajectory_induction {r : ℕ} (step : Fin r → State → Draw → State)
    (initial : State) (tape : Fin r → Draw) (P : Fin (r + 1) → State → Prop)
    (hzero : P 0 initial)
    (hstep : ∀ i, P i.castSucc (reached step initial tape i) →
      P i.succ (step i (reached step initial tape i) (tape i))) :
    ∀ i, P i (trajectory step initial tape i) := by
  apply Fin.induction
  · simpa only [trajectory_zero] using hzero
  · intro i hi
    rw [trajectory_succ, trajectory_castSucc]
    exact hstep i (by simpa only [trajectory_castSucc] using hi)

variable {n r : ℕ}

theorem trajectory_last_eq_run (policy : Policy n) (jobs : Fin r → Job n)
    (initial : LoopState n) (tape : Fin r → UpperCircular.Circle) :
    trajectory (loopTransition policy jobs) initial tape (Fin.last r) = (run policy jobs initial tape).2 := by
  induction r generalizing initial with
  | zero => rfl
  | succ r ih =>
    change trajectory (fun i => loopTransition policy jobs i.succ)
      (loopTransition policy jobs 0 initial (tape 0)) (fun i => tape i.succ) (Fin.last r) = _
    exact ih (fun i => jobs i.succ) (loopTransition policy jobs 0 initial (tape 0)) (fun i => tape i.succ)

/-- Every nonstopped reached proposal passing the actual check guarantees
that the full loop stays open, including after its last response. -/
theorem run_open_of_accepts (policy : Policy n) (jobs : Fin r → Job n)
    (initial : LoopState n) (tape : Fin r → UpperCircular.Circle) (hopen : initial.stopped = false)
    (haccept : ∀ i, (reached (loopTransition policy jobs) initial tape i).stopped = false →
      accepts (jobs i) (reached (loopTransition policy jobs) initial tape i).current
        (UpperCorrectionExecution.execute policy (reached (loopTransition policy jobs) initial tape i).current
          (jobs i).owner (jobs i).deficit (tape i)).2 = true) :
    (run policy jobs initial tape).2.stopped = false := by
  rw [← trajectory_last_eq_run]
  apply trajectory_induction (loopTransition policy jobs) initial tape (fun _ state => state.stopped = false) hopen
  intro i hi
  simp only [loopTransition, step, hi, Bool.false_eq_true, ite_false, haccept i hi, ite_true]

end EnvyFreeResearch.Full.UpperLoopTrajectory
