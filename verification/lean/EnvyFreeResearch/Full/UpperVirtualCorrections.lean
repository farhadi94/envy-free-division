import EnvyFreeResearch.Full.UpperVirtualGrid
import EnvyFreeResearch.Full.UpperLoopTrajectory

/-! Each actual reached correction has a virtual recorded-union witness.
The proof tracks accepted descriptors along the actual original tape and
includes the first rejecting proposal's two recorded endpoints. -/

noncomputable section

open Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperVirtualCorrections

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCircularStage UpperAggregateInterpolation UpperCorrectionPieces UpperCorrectionTrace
  UpperLoopTrajectory

variable {n r g : ℕ}

def EndpointIn {Index : Type*} (points : Index → ℝ) (record : Correction) : Prop :=
  (∃ i, points i = record.first) ∧ ∃ i, points i = record.last

theorem accepted_in_stream (policy : Policy n) (jobs : Fin r → Job n)
    (initial : LoopState n) (hinitial : initial.accepted = []) (tape : Fin r → UpperCircular.Circle)
    (j : Fin r) :
    ∀ record ∈ (reached (loopTransition policy jobs) initial tape j).accepted,
      EndpointIn (loopPoint policy jobs initial tape) record := by
  let P (_ : Fin (r + 1)) (state : LoopState n) :=
    ∀ record ∈ state.accepted, EndpointIn (loopPoint policy jobs initial tape) record
  have hzero : P 0 initial := by simp [P, hinitial]
  have hstep (i : Fin r) (hi : P i.castSucc (reached (loopTransition policy jobs) initial tape i)) :
      P i.succ (loopTransition policy jobs i (reached (loopTransition policy jobs) initial tape i) (tape i)) := by
    let state := reached (loopTransition policy jobs) initial tape i
    change P i.succ (step policy state (jobs i, tape i)).2
    by_cases hstop : state.stopped = true
    · rw [step_stopped policy state _ hstop]
      exact hi
    · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
      simp only [step, hopen, Bool.false_eq_true, ite_false]
      split_ifs with haccept
      · intro record hrecord
        rcases List.mem_append.mp hrecord with hrecord | hrecord
        · exact hi record hrecord
        · have heq : record = (execute policy state.current (jobs i).owner (jobs i).deficit (tape i)).1 :=
            List.mem_singleton.mp hrecord
          subst record
          have he := reached_descriptor_in_stream policy jobs initial tape i hopen
          exact ⟨⟨(i, false), he.1⟩, ⟨(i, true), he.2⟩⟩
      · exact hi
  have h := trajectory_induction (loopTransition policy jobs) initial tape P hzero hstep j.castSucc
  simpa only [trajectory_castSucc] using h

theorem reached_consistent (policy : Policy n) (jobs : Fin r → Job n)
    (origin : List Component) (initial : LoopState n) (hinitial : Consistent origin initial)
    (tape : Fin r → UpperCircular.Circle) (j : Fin r) :
    Consistent origin (reached (loopTransition policy jobs) initial tape j) := by
  have h := trajectory_induction (loopTransition policy jobs) initial tape
    (fun _ state => Consistent origin state) hinitial
    (fun i hi => step_consistent policy origin _ _ hi) j.castSucc
  simpa only [trajectory_castSucc] using h

def virtualPayment (virtual : List Component) (state : LoopState n) (record : Correction) : List Component :=
  take (remaining virtual state.accepted) record

theorem actual_payment_inter (policy : Policy n) (physical virtual : List Component) (R : Set ℝ)
    (hdom : domain physical = R ∩ domain virtual) (state : LoopState n)
    (hconsistent : Consistent physical state) (job : Job n) (start : UpperCircular.Circle) :
    payment policy state.current job.owner job.deficit start =
      R ∩ domain (virtualPayment virtual state (descriptor policy state.current job.owner job.deficit start)) := by
  have hd : domain state.current.cells = R ∩ domain (remaining virtual state.accepted) := by
    rw [hconsistent]
    exact remaining_inter R physical virtual hdom state.accepted
  rw [virtualPayment, take_domain]
  exact correctionPiece_inter R state.current.cells (remaining virtual state.accepted) hd _

theorem virtualPayment_recorded {Index : Type*} (cuts : Fin (g + 2) → ℝ) (points : Index → ℝ)
    (virtual : List Component) (hvirtual : ∀ p, Recorded virtual p → ∃ e, cuts e = p)
    (state : LoopState n) (hrecords : ∀ record ∈ state.accepted, EndpointIn points record)
    (record : Correction) (hrecord : EndpointIn points record) :
    RecordedEndpoints cuts points (virtualPayment virtual state record) := by
  have hp (p : ℝ) (hp : Recorded (virtualPayment virtual state record) p) :
      (∃ e, cuts e = p) ∨ ∃ i, points i = p := by
    rcases take_recorded _ record hp with hp | hp | hp
    · exact Or.inr (by simpa only [hp] using hrecord.1)
    · exact Or.inr (by simpa only [hp] using hrecord.2)
    · rcases remaining_recorded virtual state.accepted hp with hp | hp
      · obtain ⟨r, hr, hp⟩ := List.mem_flatMap.mp hp
        have hp' : p = r.first ∨ p = r.last := by simpa using hp
        rcases hp' with hp | hp
        · exact Or.inr (by simpa only [hp] using (hrecords r hr).1)
        · exact Or.inr (by simpa only [hp] using (hrecords r hr).2)
      · exact Or.inl (hvirtual p hp)
  intro c hc
  exact ⟨hp c.left ⟨c, hc, Or.inl rfl⟩, hp c.right ⟨c, hc, Or.inr rfl⟩⟩

/-- Complete virtual-witness contract for every nonstopped actual proposal,
whether it will pass or reject. Old physical joins are supplied solely by
intersection with `R`, and do not enter the recorded boundary indices. -/
theorem reached_payment_supported (policy : Policy n) (jobs : Fin r → Job n)
    (physical virtual : List Component) (R : Set ℝ) (hdom : domain physical = R ∩ domain virtual)
    (cuts : Fin (g + 2) → ℝ) (hvirtual : ∀ p, Recorded virtual p → ∃ e, cuts e = p)
    (initial : LoopState n) (hconsistent : Consistent physical initial) (hrecords : initial.accepted = [])
    (tape : Fin r → UpperCircular.Circle) (j : Fin r)
    (hopen : (reached (loopTransition policy jobs) initial tape j).stopped = false) :
    ∃ pieces, RecordedEndpoints cuts (loopPoint policy jobs initial tape) pieces ∧
      payment policy (reached (loopTransition policy jobs) initial tape j).current
        (jobs j).owner (jobs j).deficit (tape j) = R ∩ domain pieces := by
  let state := reached (loopTransition policy jobs) initial tape j
  let record := descriptor policy state.current (jobs j).owner (jobs j).deficit (tape j)
  refine ⟨virtualPayment virtual state record, ?_, ?_⟩
  · apply virtualPayment_recorded cuts _ virtual hvirtual state
      (accepted_in_stream policy jobs initial hrecords tape j) record
    have h := reached_descriptor_in_stream policy jobs initial tape j hopen
    exact ⟨⟨(j, false), h.1⟩, ⟨(j, true), h.2⟩⟩
  · exact actual_payment_inter policy physical virtual R hdom state
      (reached_consistent policy jobs physical initial hconsistent tape j) (jobs j) (tape j)

end EnvyFreeResearch.Full.UpperVirtualCorrections
