import EnvyFreeResearch.Full.RefinedUpperBatchUnroll

/-! A successful retry batch returns the actual accepted physical correction,
with every locally proved property. Its earlier rejected attempts preserve
pieces while allowing the oracle history to change. -/
noncomputable section
open Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperBatchVerification
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionTrace
  UpperRecordedDomain UpperDomainDifference UpperCorrectionPieces
  RefinedUpperCorrectionRetries RefinedUpperBatchUnroll
abbrev Circle := UpperCircular.Circle
variable {n r : ℕ}

theorem batch_success_properties (policy : Policy n) (job : Job n)
    (Inv : LoopState n → Prop)
    (hpreserve : ∀ s start, Inv s → s.stopped = false →
      (step policy s (job, start)).1 = true → Inv (reopen (step policy s (job, start)).2))
    (P : List Component → Prop)
    (hlocal : ∀ s start, Inv s → s.stopped = false →
      accepts job s.current (execute policy s.current job.owner job.deficit start).2 = true →
      P (take s.current.cells (descriptor policy s.current job.owner job.deficit start)))
    (s : LoopState n) (tape : Fin r → Circle) (hs : Inv s)
    (hrun : (batch policy job s tape).stopped = false) :
    ∃ record, (batch policy job s tape).accepted = s.accepted ++ [record] ∧
      (batch policy job s tape).current.cells = applyCorrection s.current.cells record ∧
      P (take s.current.cells record) := by
  induction r generalizing s with
  | zero => simp [batch_zero] at hrun
  | succ r ih =>
    have ho : s.stopped = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      rw [RefinedUpperBatchLoop.batch_stopped policy job s tape h, h] at hrun
      contradiction
    rw [batch_succ policy job s tape ho] at hrun ⊢
    split_ifs at hrun ⊢ with hr
    · have hi := hpreserve s (tape 0) hs ho hr
      obtain ⟨record, ha, hc, hp⟩ := ih (reopen (step policy s (job, tape 0)).2)
        (fun i => tape i.succ) hi hrun
      have he := step_rejected policy s job (tape 0) hr
      refine ⟨record, ?_, ?_, ?_⟩
      · simpa only [reopen, he.2] using ha
      · simpa only [reopen, he.1] using hc
      · simpa only [reopen, he.1] using hp
    · have hf : (step policy s (job, tape 0)).1 = false := Bool.eq_false_iff.mpr hr
      have hn := step_not_rejected policy s job (tape 0) ho hf
      have hstate := step_running policy s (job, tape 0) hn.1
      let record := descriptor policy s.current job.owner job.deficit (tape 0)
      refine ⟨record, ?_, ?_, hlocal s (tape 0) hs ho hn.2⟩
      · rw [hstate.2.2]
        rfl
      · rw [hstate.2.2]
        rfl

/-- Every successful recipient output inherits the proved physical local
property, despite the preceding rejected queries in every batch. -/
theorem run_success_properties {k : ℕ} (policy : Policy n) (jobs : Fin k → Job n)
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hretry : ∀ i s start, Safe i.castSucc s → s.stopped = false →
      (step policy s (jobs i, start)).1 = true →
      Safe i.castSucc (reopen (step policy s (jobs i, start)).2))
    (hpreserve : ∀ i s (tape : Fin r → Circle), Safe i.castSucc s →
      Safe i.succ (batch policy (jobs i) s tape))
    (P : Job n → List Component → Prop)
    (hlocal : ∀ i s start, Safe i.castSucc s → s.stopped = false →
      accepts (jobs i) s.current (execute policy s.current (jobs i).owner (jobs i).deficit start).2 = true →
      P (jobs i) (take s.current.cells (descriptor policy s.current (jobs i).owner (jobs i).deficit start)))
    (s : LoopState n) (tape : Fin k → Fin r → Circle) (hs : Safe 0 s)
    (hrun : (RefinedUpperBatchLoop.run policy jobs s tape).2.stopped = false) :
    ∃ records, (RefinedUpperBatchLoop.run policy jobs s tape).2.accepted = s.accepted ++ records ∧
      (RefinedUpperBatchLoop.run policy jobs s tape).2.current.cells = remaining s.current.cells records ∧
      List.Forall₂ P (List.ofFn jobs) (payments s.current.cells records) := by
  induction k generalizing s with
  | zero =>
    refine ⟨[], ?_, rfl, ?_⟩
    · simp [RefinedUpperBatchLoop.run, UpperFreshSamples.run]
    · simp [payments]
  | succ k ih =>
    change (RefinedUpperBatchLoop.run policy (fun i => jobs i.succ)
      (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ)).2.stopped = false at hrun
    have hfirstOpen := RefinedUpperBatchLoop.run_running_origin policy (fun i => jobs i.succ)
      (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ) hrun
    obtain ⟨record, ha, hc, hp⟩ := batch_success_properties policy (jobs 0) (Safe 0)
      (hretry 0) (P (jobs 0)) (hlocal 0) s (tape 0) hs hfirstOpen
    have hnextSafe := hpreserve 0 s (tape 0) hs
    obtain ⟨records, hrecords, hremaining, hproperties⟩ := ih (fun i => jobs i.succ)
      (fun i => Safe i.succ)
      (fun i s start hs hopen hr => hretry i.succ s start hs hopen hr)
      (fun i s tape hs => hpreserve i.succ s tape hs)
      (fun i s start hs hopen ha => hlocal i.succ s start hs hopen ha)
      (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ) hnextSafe hrun
    refine ⟨record :: records, ?_, ?_, ?_⟩
    · change (RefinedUpperBatchLoop.run policy (fun i => jobs i.succ)
        (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ)).2.accepted = _
      rw [hrecords, ha]
      simp [List.append_assoc]
    · change (RefinedUpperBatchLoop.run policy (fun i => jobs i.succ)
        (batch policy (jobs 0) s (tape 0)) (fun i => tape i.succ)).2.current.cells = _
      rw [hremaining, hc]
      rfl
    · rw [List.ofFn_succ, payments]
      apply List.Forall₂.cons hp
      rw [hc] at hproperties
      exact hproperties

end EnvyFreeResearch.Full.RefinedUpperBatchVerification
