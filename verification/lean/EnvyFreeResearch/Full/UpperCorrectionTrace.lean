import EnvyFreeResearch.Full.UpperCorrectionPieces
import EnvyFreeResearch.Full.UpperCorrectionLoop

/-!
# Actual stopped-loop records and physical output reconstruction

Successful runs retain exactly one record for every job. The state and all
literal finite correction outputs are reconstructed from those records.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionTrace

open UpperRecordedDomain UpperDomainDifference UpperCorrectionPieces UpperCorrectionExecution
  UpperCorrectionLoop UpperCircularStage

abbrev Circle := UpperCircular.Circle

variable {n m : ℕ}

def Consistent (origin : List Component) (state : LoopState n) : Prop :=
  state.current.cells = remaining origin state.accepted

theorem initial_consistent (state : State n) : Consistent state.cells (initial state) := rfl

theorem step_consistent (policy : Policy n) (origin : List Component) (state : LoopState n)
    (draw : Job n × Circle) (hstate : Consistent origin state) :
    Consistent origin (step policy state draw).2 := by
  by_cases hstop : state.stopped = true
  · rw [step_stopped policy state draw hstop]
    exact hstate
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
    simp only [step, hopen, Bool.false_eq_true, ite_false]
    split_ifs
    · change applyCorrection state.current.cells (descriptor policy state.current draw.1.owner draw.1.deficit draw.2) =
        remaining origin (state.accepted ++ [descriptor policy state.current draw.1.owner draw.1.deficit draw.2])
      rw [remaining_append, remaining, remaining, ← hstate]
    · exact hstate

theorem step_domain_subset (policy : Policy n) (state : LoopState n) (draw : Job n × Circle) :
    domain (step policy state draw).2.current.cells ⊆ domain state.current.cells := by
  by_cases hstop : state.stopped = true
  · rw [step_stopped policy state draw hstop]
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
    simp only [step, hopen, Bool.false_eq_true, ite_false]
    split_ifs
    · rw [execute_domain]
      exact sdiff_subset
    · exact Subset.rfl

theorem run_succ_state (policy : Policy n) (jobs : Fin (m + 1) → Job n)
    (state : LoopState n) (tape : Fin (m + 1) → Circle) :
    (run policy jobs state tape).2 =
      (run policy (fun i => jobs i.succ) (step policy state (jobs 0, tape 0)).2 (fun i => tape i.succ)).2 := rfl

theorem run_consistent (policy : Policy n) (jobs : Fin m → Job n) (origin : List Component)
    (state : LoopState n) (tape : Fin m → Circle) (hstate : Consistent origin state) :
    Consistent origin (run policy jobs state tape).2 := by
  induction m generalizing state with
  | zero => exact hstate
  | succ m ih =>
    rw [run_succ_state]
    exact ih _ _ _ (step_consistent policy origin state _ hstate)

theorem run_domain_subset (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) : domain (run policy jobs state tape).2.current.cells ⊆ domain state.current.cells := by
  induction m generalizing state with
  | zero => exact Subset.rfl
  | succ m ih =>
    rw [run_succ_state]
    exact (ih _ _ _).trans (step_domain_subset policy state _)

theorem run_stopped (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) (hstop : state.stopped = true) : (run policy jobs state tape).2 = state := by
  induction m generalizing state with
  | zero => rfl
  | succ m ih =>
    rw [run_succ_state, step_stopped policy state (jobs 0, tape 0) hstop]
    exact ih _ _ _ hstop

theorem run_running_origin (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) (hrun : (run policy jobs state tape).2.stopped = false) : state.stopped = false := by
  apply Bool.eq_false_iff.mpr
  intro hstop
  rw [run_stopped policy jobs state tape hstop, hstop] at hrun
  contradiction

theorem step_running (policy : Policy n) (state : LoopState n) (draw : Job n × Circle)
    (hrun : (step policy state draw).2.stopped = false) :
    state.stopped = false ∧
      accepts draw.1 state.current (execute policy state.current draw.1.owner draw.1.deficit draw.2).2 = true ∧
      (step policy state draw).2 =
        ⟨(execute policy state.current draw.1.owner draw.1.deficit draw.2).2, false,
          state.accepted ++ [(execute policy state.current draw.1.owner draw.1.deficit draw.2).1]⟩ := by
  by_cases hstop : state.stopped = true
  · rw [step_stopped policy state draw hstop, hstop] at hrun
    contradiction
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
    simp only [step, hopen, Bool.false_eq_true, ite_false] at hrun ⊢
    split_ifs at hrun with haccept
    · exact ⟨True.intro, haccept, by rw [ite_eq_left haccept]⟩

theorem run_accepted_length (policy : Policy n) (jobs : Fin m → Job n) (state : LoopState n)
    (tape : Fin m → Circle) (hrun : (run policy jobs state tape).2.stopped = false) :
    (run policy jobs state tape).2.accepted.length = state.accepted.length + m := by
  induction m generalizing state with
  | zero => simp [run, UpperFreshSamples.run]
  | succ m ih =>
    rw [run_succ_state] at hrun ⊢
    have hfirst := run_running_origin policy (fun i => jobs i.succ)
      (step policy state (jobs 0, tape 0)).2 (fun i => tape i.succ) hrun
    have h := step_running policy state (jobs 0, tape 0) hfirst
    rw [ih _ _ _ hrun, h.2.2]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Successful output reconstruction returns one finite payment per actual
job, with pairwise literal disjointness and a literal remaining complement. -/
theorem successful_outputs (policy : Policy n) (jobs : Fin m → Job n) (origin : State n)
    (tape : Fin m → Circle) (hrun : (run policy jobs (initial origin) tape).2.stopped = false) :
    let final := (run policy jobs (initial origin) tape).2
    (payments origin.cells final.accepted).length = m ∧
      (payments origin.cells final.accepted).Pairwise (fun a b => Disjoint (domain a) (domain b)) ∧
      domain final.current.cells = domain origin.cells \ domain (payments origin.cells final.accepted).flatten := by
  dsimp only
  have hc := run_consistent policy jobs origin.cells (initial origin) tape (initial_consistent origin)
  have hl := run_accepted_length policy jobs (initial origin) tape hrun
  refine ⟨?_, payments_disjoint _ _, ?_⟩
  · rw [payments_length]
    simpa only [initial, List.length_nil, Nat.zero_add] using hl
  · rw [hc, remaining_domain, payments_flatten_domain]

end EnvyFreeResearch.Full.UpperCorrectionTrace
