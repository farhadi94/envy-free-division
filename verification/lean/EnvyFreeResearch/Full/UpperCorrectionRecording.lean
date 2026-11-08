import EnvyFreeResearch.Full.UpperComponentFamily
import EnvyFreeResearch.Full.UpperCorrectionOutcome

/-! Every actually generated correction endpoint remains in the complete
history, including after a rejected attempt. These facts make the assembled
payment states suitable as later cached inputs. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionRecording

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache
  UpperCorrectionLoop UpperCorrectionTrace UpperCorrectionPieces UpperCircularStage

variable {n m : ℕ}

def RecordedEndpoints (records : List Correction) (history : History n) : Prop :=
  ∀ i p, p ∈ endpoints records → ∃ answer, (IntervalOracle.Query.eval i 0 p, answer) ∈ history

theorem recordedEndpoints_mono (records : List Correction) {old new : History n}
    (h : RecordedEndpoints records old) (hext : old ⊆ new) : RecordedEndpoints records new := by
  intro i p hp
  obtain ⟨answer, ha⟩ := h i p hp
  exact ⟨answer, hext ha⟩

theorem descriptor_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain state.cells)) (eps : ℝ) (start : UpperCircular.Circle) :
    RecordedEndpoints [descriptor policy state cutter eps start] (execute policy state cutter eps start).2.history := by
  have h := circular_history μ policy hpolicy state.history cutter (values state cutter) state.cells hstate.2.1
    hstate.2.2.1 hstate.2.2.2 (values_correct μ state hstate cutter) hpositive (amount eps (total state cutter)) start
  rw [total_correct μ state hstate cutter] at h
  intro i p hp
  simp only [endpoints, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simpa only [descriptor, execute, recordedCorrection, total_correct μ state hstate cutter] using h.2.2.1 i
  · simpa only [descriptor, execute, recordedCorrection, total_correct μ state hstate cutter] using h.2.2.2 i

theorem step_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (state : LoopState n) (hstate : WellFormed μ state.current) (draw : Job n × UpperCircular.Circle)
    (hpositive : state.stopped = false → 0 < (μ draw.1.owner).real (domain state.current.cells))
    (hrecorded : RecordedEndpoints state.accepted state.current.history) :
    state.current.history ⊆ (step policy state draw).2.current.history ∧
      RecordedEndpoints (step policy state draw).2.accepted (step policy state draw).2.current.history := by
  by_cases hs : state.stopped = true
  · rw [step_stopped policy state draw hs]
    exact ⟨Subset.rfl, hrecorded⟩
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hs
    have hh := execute_history μ policy hpolicy state.current hstate draw.1.owner (hpositive hopen) draw.1.deficit draw.2
    have hr := recordedEndpoints_mono state.accepted hrecorded hh.2
    have hn := descriptor_recorded μ policy hpolicy state.current hstate draw.1.owner (hpositive hopen) draw.1.deficit draw.2
    simp only [step, hopen, Bool.false_eq_true, ite_false]
    split_ifs
    · refine ⟨hh.2, ?_⟩
      intro i p hp
      change p ∈ endpoints (state.accepted ++ [descriptor policy state.current draw.1.owner draw.1.deficit draw.2]) at hp
      rw [endpoints, List.flatMap_append, List.mem_append] at hp
      exact hp.elim (hr i p) (hn i p)
    · exact ⟨hh.2, hr⟩

/-- Finite execution preserves a time-indexed invariant through its actual
last step, including a final rejected step. -/
theorem run_invariant (policy : Policy n) (jobs : Fin m → Job n)
    (Inv : Fin (m + 1) → LoopState n → Prop)
    (hstep : ∀ i state start, Inv i.castSucc state → Inv i.succ (step policy state (jobs i, start)).2)
    (initial : LoopState n) (tape : Fin m → UpperCircular.Circle) (hinit : Inv 0 initial) :
    Inv (Fin.last m) (run policy jobs initial tape).2 := by
  induction m generalizing initial with
  | zero => exact hinit
  | succ m ih =>
    rw [run_succ_state]
    exact ih (fun i => jobs i.succ) (fun i => Inv i.succ)
      (fun i state start h => hstep i.succ state start h)
      (step policy initial (jobs 0, tape 0)).2 (fun i => tape i.succ) (hstep 0 initial (tape 0) hinit)

theorem run_recorded (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (jobs : Fin m → Job n) (Safe : Fin (m + 1) → LoopState n → Prop)
    (hstep : ∀ i state start, Safe i.castSucc state → Safe i.succ (step policy state (jobs i, start)).2)
    (hready : ∀ i state, Safe i.castSucc state → WellFormed μ state.current ∧
      (state.stopped = false → 0 < (μ (jobs i).owner).real (domain state.current.cells)))
    (initial : LoopState n) (tape : Fin m → UpperCircular.Circle) (hinit : Safe 0 initial)
    (hrecords : RecordedEndpoints initial.accepted initial.current.history) :
    Safe (Fin.last m) (run policy jobs initial tape).2 ∧
      initial.current.history ⊆ (run policy jobs initial tape).2.current.history ∧
      RecordedEndpoints (run policy jobs initial tape).2.accepted (run policy jobs initial tape).2.current.history := by
  apply run_invariant policy jobs
    (fun time state => Safe time state ∧ initial.current.history ⊆ state.current.history ∧
      RecordedEndpoints state.accepted state.current.history) _ initial tape ⟨hinit, Subset.rfl, hrecords⟩
  intro i state start hs
  have hr := step_recorded μ policy hpolicy state (hready i state hs.1).1 (jobs i, start)
    (hready i state hs.1).2 hs.2.2
  exact ⟨hstep i state start hs.1, (fun _ hx => hr.1 (hs.2.1 hx)), hr.2⟩

theorem payments_components_disjoint (cs : List Component) (hcs : DisjointComponents cs)
    (records : List Correction) (piece : List Component) (hpiece : piece ∈ payments cs records) :
    DisjointComponents piece := by
  induction records generalizing cs with
  | nil => simp [payments] at hpiece
  | cons r records ih =>
    rcases List.mem_cons.mp hpiece with rfl | hp
    · exact take_disjoint cs hcs r
    · exact ih _ (removeCorrection_disjoint cs hcs r.amount r.start r.first r.last) hp

theorem payments_recordedHistory (cs : List Component) (records : List Correction) (history : History n)
    (hcs : RecordedHistory cs history) (hrecords : RecordedEndpoints records history)
    (piece : List Component) (hpiece : piece ∈ payments cs records) : RecordedHistory piece history := by
  intro i p hp
  exact (payments_recorded cs records piece hpiece hp).elim (hrecords i p) (hcs i p)

end EnvyFreeResearch.Full.UpperCorrectionRecording
