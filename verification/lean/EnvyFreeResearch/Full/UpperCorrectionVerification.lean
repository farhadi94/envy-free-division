import EnvyFreeResearch.Full.UpperCorrectionTrace

/-!
# Per-payment correctness for the full actual successful loop

A local accepted-transaction property is propagated through the actual
history-dependent run. The conclusion is about its concrete recorded
finite-component outputs, not an assumed list of successful corrections.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionVerification

open UpperRecordedDomain UpperDomainDifference UpperCorrectionPieces UpperCorrectionExecution
  UpperCorrectionLoop UpperCircularStage UpperCorrectionTrace

abbrev Circle := UpperCircular.Circle

variable {n m : ℕ}

/-- Success forces every attempted transaction to have passed its check.
The generated records and their physical outputs obey every proved local
accepted-transaction property. -/
theorem run_success_properties (policy : Policy n) (jobs : Fin m → Job n)
    (Safe : Fin (m + 1) → LoopState n → Prop)
    (hpreserve : ∀ i state start, Safe i.castSucc state →
      Safe i.succ (step policy state (jobs i, start)).2)
    (P : Job n → List Component → Prop)
    (hlocal : ∀ i state start, Safe i.castSucc state → state.stopped = false →
      accepts (jobs i) state.current (execute policy state.current (jobs i).owner (jobs i).deficit start).2 = true →
      P (jobs i) (take state.current.cells (descriptor policy state.current (jobs i).owner (jobs i).deficit start)))
    (state : LoopState n) (tape : Fin m → Circle) (hsafe : Safe 0 state)
    (hrun : (run policy jobs state tape).2.stopped = false) :
    ∃ records, (run policy jobs state tape).2.accepted = state.accepted ++ records ∧
      (run policy jobs state tape).2.current.cells = remaining state.current.cells records ∧
      List.Forall₂ P (List.ofFn jobs) (payments state.current.cells records) := by
  induction m generalizing state with
  | zero =>
    refine ⟨[], ?_, rfl, ?_⟩
    · simp [run, UpperFreshSamples.run]
    · simp [payments]
  | succ m ih =>
    rw [run_succ_state] at hrun
    have hfirstOpen := run_running_origin policy (fun i => jobs i.succ)
      (step policy state (jobs 0, tape 0)).2 (fun i => tape i.succ) hrun
    have hfirst := step_running policy state (jobs 0, tape 0) hfirstOpen
    have hhead := hlocal 0 state (tape 0) hsafe hfirst.1 hfirst.2.1
    have hnextSafe := hpreserve 0 state (tape 0) hsafe
    obtain ⟨records, hrecords, hremaining, hproperties⟩ := ih (fun i => jobs i.succ)
      (fun i => Safe i.succ)
      (fun i state start hs => hpreserve i.succ state start hs)
      (fun i state start hs hopen hcheck => hlocal i.succ state start hs hopen hcheck)
      (step policy state (jobs 0, tape 0)).2 (fun i => tape i.succ) hnextSafe hrun
    let record := descriptor policy state.current (jobs 0).owner (jobs 0).deficit (tape 0)
    refine ⟨record :: records, ?_, ?_, ?_⟩
    · rw [run_succ_state, hrecords, hfirst.2.2]
      change (state.accepted ++ [record]) ++ records = state.accepted ++ record :: records
      simp [List.append_assoc]
    · rw [run_succ_state, hremaining, hfirst.2.2]
      rfl
    · rw [List.ofFn_succ, payments]
      apply List.Forall₂.cons hhead
      rw [hfirst.2.2] at hproperties
      exact hproperties

end EnvyFreeResearch.Full.UpperCorrectionVerification
