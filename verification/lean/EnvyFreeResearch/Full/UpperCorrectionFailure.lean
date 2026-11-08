import EnvyFreeResearch.Full.UpperCorrectionError
import EnvyFreeResearch.Full.UpperVirtualCorrections

/-! Actual correction rejection is contained in the two proved analytic
failure events. The physical interpolation witness is constructed by virtual
replay of the actual accepted descriptors, including the rejecting proposal. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionFailure

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperCorrectionSupply UpperRawPayments UpperEnvelope
  UpperPayments UpperCircularStage UpperStageMeasurable UpperPreparedEnvelopeMean
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity UpperVirtualCorrections

variable {n k m : ℕ} [Nonempty (Fin k)]

theorem table_eq_physicalRows (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (hreserve : WellFormed μ reserve) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells) :
    table active reserve cuts = physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts := by
  funext i e
  exact table_correct μ active reserve hreserve cuts hzero hmono hsep i e

theorem interpolation_bound (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam N b : ℝ)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (tape : Fin k → UpperCircular.Circle)
    (hgood : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts
      (loopPoint policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape) b)
    (j : Fin k)
    (hopen : (reached (loopTransition policy (tasks active reserve cuts t eta lam))
      (startState active reserve cuts t eta) tape j).stopped = false) (i : Fin k) :
    let C := payment policy (reached (loopTransition policy (tasks active reserve cuts t eta lam))
      (startState active reserve cuts t eta) tape j).current
        (active j) (tasks active reserve cuts t eta lam j).deficit (tape j)
    |(μ (active i)).real C / (μ (active i)).real (domain reserve.cells) -
      (μ (active j)).real C / (μ (active j)).real (domain reserve.cells) -
      estimate (table active reserve cuts) (uniformCells (cell (domain reserve.cells) cuts)) i j C| ≤
      b * distance (table active reserve cuts) i j := by
  let virtual := UpperVirtualGrid.initial cuts (whole active reserve cuts t eta)
  let initial := startState active reserve cuts t eta
  have hdom : domain initial.current.cells = domain reserve.cells ∩ domain virtual :=
    UpperVirtualGrid.physical_initial_inter reserve hc.wellFormed.2.1 cuts hc.zero hc.monotone hc.separated _
  have hrecorded (p : ℝ) (hp : Recorded virtual p) : ∃ e, cuts e = p :=
    UpperVirtualGrid.initial_recorded cuts hc.zero hc.one _ hp
  obtain ⟨pieces, hends, hactual⟩ := reached_payment_supported policy (tasks active reserve cuts t eta lam)
    initial.current.cells virtual (domain reserve.cells) hdom cuts hrecorded initial
    (by rfl) (by rfl) tape j hopen
  apply le_of_not_gt
  intro hbad
  apply hgood
  refine ⟨i, j, pieces, _, hends, hactual, ?_⟩
  have howner : (tasks active reserve cuts t eta lam j).owner = active j := rfl
  simpa only [howner, initial, ← table_eq_physicalRows μ active reserve cuts hc.wellFormed hc.zero hc.monotone hc.separated]
    using hbad

/-- Every concrete cached proposal passes outside the two simultaneous
analytic failure events, so the actual stopped program returns successfully. -/
theorem run_open_of_no_errors (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N b : ℝ) (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hb : 0 ≤ b)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * N ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (tape : Fin k → UpperCircular.Circle)
    (hestimate : tape ∉ UpperEnvelopeLoop.bad policy (tasks active reserve cuts t eta lam)
      (table active reserve cuts) (uniformCells (cell (domain reserve.cells) cuts)) id lam
      (startState active reserve cuts t eta))
    (hinterpolation : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts
      (loopPoint policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape) b) :
    (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false := by
  let jobs := tasks active reserve cuts t eta lam
  let initial := startState active reserve cuts t eta
  let Safe := UpperCorrectionSupply.Safe μ (activeSet active) (domain reserve.cells)
    (fun i => 7 / 8 * (μ i).real (domain reserve.cells)) jobs
  have hfullsize : (k : ℝ)^2 ≤ lam := by linarith
  have hpreserve (j : Fin k) (state : LoopState n) (start : UpperCircular.Circle)
      (hs : Safe j.castSucc state) : Safe j.succ (loopTransition policy jobs j state start) :=
    tasks_safe_step μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive policy hpolicy
      (domain reserve.cells) t eta lam heta hc.small hc.targets hc.sum hfullsize j state start hs
  have hinit : Safe 0 initial := start_safe μ active reserve hc.wellFormed cuts hc.zero hc.monotone
    hc.separated hc.positive hinj (domain reserve.cells) Subset.rfl t eta lam heta hlam hc.small hc.sum hmargin
  apply UpperLoopTrajectory.run_open_of_accepts policy jobs initial tape rfl
  intro j hopen
  have hs := UpperEnvelopeLoop.reached_invariant _ Safe hpreserve initial tape hinit j
  apply UpperCorrectionError.accepts_of_errors μ policy hpolicy active hinj reserve cuts t eta lam N b
    heta hlam hb hsize hquarter selected hc (domain reserve.cells) j _ hs (tape j)
  · intro i
    apply le_of_not_gt
    intro hbad
    exact hestimate ⟨j, hopen, i, hbad⟩
  · exact interpolation_bound μ policy active reserve cuts t eta lam N b selected hc tape hinterpolation j hopen

/-- The concrete rejection event is covered by one envelope event and one
simultaneous interpolation event, with no pair/recipient union factor. -/
theorem rejection_subset (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N b : ℝ) (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hb : 0 ≤ b)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * N ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N) :
    {tape | (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = true} ⊆
      UpperEnvelopeLoop.bad policy (tasks active reserve cuts t eta lam) (table active reserve cuts)
        (uniformCells (cell (domain reserve.cells) cuts)) id lam (startState active reserve cuts t eta) ∪
      {tape | BadSupportedRecordedUnion (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts
        (loopPoint policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape) b} := by
  intro tape htape
  by_contra h
  have hnot := not_or.mp h
  have hopen := run_open_of_no_errors μ policy hpolicy active hinj reserve cuts t eta lam N b
    heta hlam hb hsize hquarter hmargin selected hc tape hnot.1 hnot.2
  simp only [Set.mem_setOf_eq, hopen, Bool.false_eq_true] at htape

end EnvyFreeResearch.Full.UpperCorrectionFailure
