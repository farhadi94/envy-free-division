import EnvyFreeResearch.Full.RefinedUpperBatchLoop

/-! First-success recursion for the literal finite retry implementation. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperBatchUnroll
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop RefinedUpperCorrectionRetries
abbrev Circle := UpperCircular.Circle
variable {n r : ℕ}

theorem retry_done (policy : Policy n) (job : Job n) (s : LoopState n) (tape : Fin r → Circle) :
    (UpperFreshSamples.run (attempt policy) r (true, s) (fun i => (job, tape i))).2 = (true, s) := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [UpperFreshSamples.run, attempt] using ih (fun i => tape i.succ)

theorem step_rejected (policy : Policy n) (s : LoopState n) (job : Job n) (start : Circle)
    (hr : (step policy s (job, start)).1 = true) :
    (step policy s (job, start)).2.current.cells = s.current.cells ∧
    (step policy s (job, start)).2.accepted = s.accepted := by
  unfold step at hr ⊢
  split_ifs at hr ⊢ <;> simp_all
  split_ifs at hr ⊢ <;> simp_all

theorem step_not_rejected (policy : Policy n) (s : LoopState n) (job : Job n) (start : Circle)
    (ho : s.stopped = false) (hr : (step policy s (job, start)).1 = false) :
    (step policy s (job, start)).2.stopped = false ∧
    accepts job s.current (execute policy s.current job.owner job.deficit start).2 = true := by
  simp only [step, ho, Bool.false_eq_true, ite_false] at hr ⊢
  split_ifs at hr ⊢ <;> simp_all

theorem batch_zero (policy : Policy n) (job : Job n) (s : LoopState n) (tape : Fin 0 → Circle) :
    batch policy job s tape = ⟨s.current, true, s.accepted⟩ := by
  simp [batch, retry, UpperFreshSamples.run, finish]

theorem batch_succ (policy : Policy n) (job : Job n) (s : LoopState n)
    (tape : Fin (r + 1) → Circle) (ho : s.stopped = false) :
    batch policy job s tape =
      if (step policy s (job, tape 0)).1 then
        batch policy job (reopen (step policy s (job, tape 0)).2) (fun i => tape i.succ)
      else reopen (step policy s (job, tape 0)).2 := by
  unfold batch retry
  simp only [UpperFreshSamples.run, attempt, ho, Bool.false_or, Bool.false_eq_true, ite_false, update]
  by_cases hr : (step policy s (job, tape 0)).1 = true
  · simp only [hr, Bool.not_true, ite_true]
  · have hf : (step policy s (job, tape 0)).1 = false := Bool.eq_false_iff.mpr hr
    simp only [hf, Bool.not_false, Bool.false_eq_true, ite_false]
    rw [retry_done]
    simp [finish, reopen]

end EnvyFreeResearch.Full.RefinedUpperBatchUnroll
