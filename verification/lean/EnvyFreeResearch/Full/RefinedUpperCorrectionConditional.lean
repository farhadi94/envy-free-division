import EnvyFreeResearch.Full.RefinedUpperCorrectionError
import EnvyFreeResearch.Full.RefinedUpperRetainedGeometry
import EnvyFreeResearch.Full.RefinedUpperCorrectionChance
import EnvyFreeResearch.Full.RefinedUpperRetryFailure
import EnvyFreeResearch.Full.UpperCorrectionFailure

/-! Conditional rejection for the actual retried correction. All inherited
accepted endpoints are charged; failed attempts change only the query history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionConditional
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop RefinedUpperCorrectionSetup UpperCorrectionSupply RefinedUpperRawPayments
  UpperEnvelope RefinedUpperPayments UpperCircularStage UpperPreparedEnvelopeMean
  UpperAggregateInterpolation UpperGridInterpolation UpperCorrectionTrace
  RefinedUpperCorrectionChance UpperEnvelopeCharge
open UpperPayments (cellGap cellGap_nonneg)
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem interpolation_bound (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam N : ℝ)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (s : LoopState n)
    (hconsistent : Consistent (startState active reserve cuts t eta).current.cells s)
    (hcount : s.accepted.length < k) (j : Fin k) (start : UpperCircular.Circle)
    (hprior : ∀ i record, record ∈ s.accepted →
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts record.first i j ≤
          2 * cellGap (table active reserve cuts) i j ∧
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts record.last i j ≤
          2 * cellGap (table active reserve cuts) i j)
    (hnew : ∀ i,
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts
        (descriptor policy s.current (active j) (tasks active reserve cuts t eta lam j).deficit start).first i j ≤
          2 * cellGap (table active reserve cuts) i j ∧
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts
        (descriptor policy s.current (active j) (tasks active reserve cuts t eta lam j).deficit start).last i j ≤
          2 * cellGap (table active reserve cuts) i j) :
    ∀ i, let C := payment policy s.current (active j) (tasks active reserve cuts t eta lam j).deficit start;
      |(μ (active i)).real C / (μ (active i)).real (domain reserve.cells) -
        (μ (active j)).real C / (μ (active j)).real (domain reserve.cells) -
        estimate (table active reserve cuts) (uniformCells (cell (domain reserve.cells) cuts)) i j C| ≤
          4 * (k : ℝ) * cellGap (table active reserve cuts) i j := by
  intro i
  let virtual := UpperVirtualGrid.initial cuts (whole active reserve cuts t eta)
  have hd : domain (startState active reserve cuts t eta).current.cells =
      domain reserve.cells ∩ domain virtual :=
    UpperVirtualGrid.physical_initial_inter reserve hc.wellFormed.2.1 cuts hc.zero hc.monotone hc.separated _
  have hv : ∀ p, Recorded virtual p → ∃ e, cuts e = p :=
    fun _ hp => UpperVirtualGrid.initial_recorded cuts hc.zero hc.one _ hp
  have h := RefinedUpperRetainedGeometry.candidate_error (fun i => μ (active i))
    (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells
    (startState active reserve cuts t eta).current.cells virtual hd cuts hc.monotone hc.zero hv
    policy s hconsistent (tasks active reserve cuts t eta lam j) start hcount i j
    (cellGap (table active reserve cuts) i j) (cellGap_nonneg _ _ _)
    (hprior i) (hnew i)
  have ht : table active reserve cuts = physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts :=
    UpperCorrectionFailure.table_eq_physicalRows μ active reserve cuts
      hc.wellFormed hc.zero hc.monotone hc.separated
  have howner : (tasks active reserve cuts t eta lam j).owner = active j := rfl
  simpa only [← ht, howner] using h

/-- The maximum-cell envelope controls all observers in one event. -/
theorem estimates_of_small_charge (policy : Policy n) (job : Job n) (s : LoopState n)
    (hdis : DisjointComponents s.current.cells) (ho : s.stopped = false)
    (a : Fin k → Fin (m + 1) → ℝ) (cells : Fin (m + 1) → Set ℝ)
    (j : Fin k) (lam : ℝ) (start : UpperCircular.Circle)
    (hsmall : ¬ ENNReal.ofReal (lam / 4) ≤
      charge (envelope a (uniformCells cells) j) policy job s start) :
    ∀ i, |estimate a (uniformCells cells) i j
      (payment policy s.current job.owner job.deficit start)| ≤ lam * cellGap a i j / 4 := by
  intro i
  apply le_of_not_gt
  intro hi
  apply hsmall
  rw [charge_eq_mass _ policy job s start hdis ho]
  exact ENNReal.ofReal_le_ofReal
    (estimated_exceed_implies_envelope a (uniformCells cells) j _ lam ⟨i, hi⟩).le

/-- On a good history, rejection with good new endpoints is covered by
one maximum-cell-envelope event, independently of the number of observers. -/
theorem good_rejection_subset (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 16 * (k : ℝ) ≤ lam)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (buffer : Set ℝ) (j : Fin k) (s : LoopState n) (ho : s.stopped = false)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc s)
    (hconsistent : Consistent (startState active reserve cuts t eta).current.cells s)
    (hcount : s.accepted.length < k)
    (bad : Set ℝ)
    (hprior : ∀ i record, record ∈ s.accepted →
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts record.first i j ≤
          2 * cellGap (table active reserve cuts) i j ∧
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts record.last i j ≤
          2 * cellGap (table active reserve cuts) i j)
    (hgood : ∀ x, x ∉ bad → ∀ i,
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts x i j ≤
          2 * cellGap (table active reserve cuts) i j) :
    {start | RefinedUpperRetryFailure.again policy (tasks active reserve cuts t eta lam j)
        (endpointBad policy (tasks active reserve cuts t eta lam j) bad) s start = true} ⊆
      {start | ENNReal.ofReal (lam / 4) ≤
        charge (envelope (table active reserve cuts)
          (uniformCells (cell (domain reserve.cells) cuts)) j)
          policy (tasks active reserve cuts t eta lam j) s start} := by
  intro start hg
  by_contra hcharge
  have howner : (tasks active reserve cuts t eta lam j).owner = active j := rfl
  have hparts : endpointBad policy (tasks active reserve cuts t eta lam j) bad s start = false ∧
      (step policy s (tasks active reserve cuts t eta lam j, start)).1 = true := by
    simpa [RefinedUpperRetryFailure.again] using hg
  have hend : (descriptor policy s.current (active j)
        (tasks active reserve cuts t eta lam j).deficit start).first ∉ bad ∧
      (descriptor policy s.current (active j)
        (tasks active reserve cuts t eta lam j).deficit start).last ∉ bad := by
    simpa only [endpointBad, ho, Bool.false_eq_true, ite_false, decide_eq_false_iff_not, not_or, howner]
      using hparts.1
  have hnew := fun i => And.intro (hgood _ hend.1 i) (hgood _ hend.2 i)
  have hi := interpolation_bound μ policy active reserve cuts t eta lam N selected hc s
    hconsistent hcount j start hprior hnew
  have he := estimates_of_small_charge policy (tasks active reserve cuts t eta lam j) s
    hsafe.1.2.1 ho (table active reserve cuts) (cell (domain reserve.cells) cuts) j lam start hcharge
  have ha := RefinedUpperCorrectionError.accepts_of_errors μ policy hp active hinj reserve cuts t
    eta lam N heta hlam hsize selected hc buffer j s hsafe start he hi
  simpa only [step, ho, Bool.false_eq_true, ite_false, howner, ha, ite_true, Prod.fst] using hparts.2

end EnvyFreeResearch.Full.RefinedUpperCorrectionConditional
