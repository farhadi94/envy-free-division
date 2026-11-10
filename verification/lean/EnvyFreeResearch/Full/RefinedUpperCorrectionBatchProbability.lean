import EnvyFreeResearch.Full.RefinedUpperCorrectionGood
import EnvyFreeResearch.Full.RefinedUpperCorrectionProbability
import EnvyFreeResearch.Full.RefinedUpperBatchChance

/-! Full conditional probability for the literal physical correction loop.
The analytic invariant includes supply, accepted endpoint history, and exact
record count. Every invariant transport is proved from the actual executor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionBatchProbability
open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop RefinedUpperCorrectionSetup UpperCorrectionSupply RefinedUpperRawPayments
  UpperEnvelope RefinedUpperPayments UpperCircularStage UpperPreparedEnvelopeMean
  UpperAggregateInterpolation UpperGridInterpolation UpperCorrectionTrace UpperStageMeasurable
  RefinedUpperCorrectionChance RefinedUpperCorrectionGood
open UpperPayments (cellGap)
variable {n k m : ℕ} [Nonempty (Fin k)]

theorem stopped_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hsize : 16 * (k : ℝ) ≤ lam) (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
    (bad : Set ℝ) (hb : MeasurableSet bad)
    (hgood : ∀ x, x ∉ bad → ∀ i j,
      physicalError (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts x i j ≤
          2 * cellGap (table active reserve cuts) i j)
    (originalMass : Fin k → ℝ) (hpos : ∀ j, 0 < originalMass j)
    (hhalf : ∀ j, originalMass j / 2 ≤ (μ (active j)).real (domain reserve.cells))
    (δ : ℝ≥0∞)
    (hbadmass : ∀ j, ((μ (active j)).restrict (domain reserve.cells)) bad ≤
      ENNReal.ofReal (originalMass j * (k : ℝ)) * δ)
    (a b B : ℝ≥0∞) (hbadbound : ENNReal.ofReal (32 * (k : ℝ) / 7) * δ ≤ a)
    (henvelope : ENNReal.ofReal (8 * eta * N / lam) ≤ b)
    (hfixed : a + B * b ≤ B) (r : ℕ) :
    UpperAdaptiveProduct.tapeLaw
      (UpperAdaptiveProduct.tapeLaw (volume : Measure UpperCircular.Circle) r) k
      {tape | (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam)
        (startState active reserve cuts t eta) tape).2.stopped = true} ≤
      (k : ℝ≥0∞) * (B + b ^ r) := by
  let jobs := tasks active reserve cuts t eta lam
  let initial := startState active reserve cuts t eta
  let floor := fun i => 7 / 8 * (μ i).real (domain reserve.cells)
  let Good : Fin (k + 1) → LoopState n → Prop := fun time s =>
    Safe μ (activeSet active) (domain reserve.cells) floor jobs time s ∧
      HistoryGood initial.current.cells bad time.val s
  let badEvent := fun j => endpointBad policy (jobs j) bad
  have hsmallsize : 4 * (k : ℝ) ≤ lam := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hfloor : ∀ i ∈ activeSet active, 0 < floor i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mul_pos (by norm_num) (hc.positive j)
  have howner : ∀ j, (jobs j).owner ∈ activeSet active := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hchecked : ∀ j i, i ∈ activeSet active → (jobs j).checked i = true := by
    intro j i hi
    simpa only [jobs, tasks, recordedJobs, RefinedUpperRawPayments.jobs, decide_eq_true_eq] using hi
  have hbudget : ∀ j i, i ∈ activeSet active → 0 ≤ budget (jobs j) i := by
    intro j i _
    exact tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
      hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsmallsize j i
  have hretry : ∀ j s d, Good j.castSucc s → s.stopped = false → badEvent j s d = false →
      (step policy s (jobs j, d)).1 = true →
      Good j.castSucc (RefinedUpperRetryFailure.next policy (jobs j) s d) := by
    intro j s d hs ho _ hr
    refine ⟨?_, next_rejected policy (jobs j) initial.current.cells bad j.val s d hs.2 ho hr⟩
    have h := supply_next μ policy hp (activeSet active) (domain reserve.cells) floor
      hfloor jobs howner hchecked hbudget j s d hs.1 ho
    simpa only [hr, ite_true] using h
  have haccept : ∀ j s d, Good j.castSucc s → s.stopped = false → badEvent j s d = false →
      (step policy s (jobs j, d)).1 = false →
      Good j.succ (RefinedUpperRetryFailure.next policy (jobs j) s d) := by
    intro j s d hs ho he hr
    refine ⟨?_, next_accepted policy (jobs j) initial.current.cells bad j.val s d hs.2 ho he hr⟩
    have h := supply_next μ policy hp (activeSet active) (domain reserve.cells) floor
      hfloor jobs howner hchecked hbudget j s d hs.1 ho
    simpa only [hr, Bool.false_eq_true, ite_false] using h
  have hbad : ∀ j s, Good j.castSucc s → s.stopped = false →
      (volume : Measure UpperCircular.Circle) {d | badEvent j s d = true} ≤ a := by
    intro j s hs _
    exact (RefinedUpperCorrectionProbability.endpoint_probability μ policy hp hm active reserve cuts t
      eta lam N heta hsmallsize selected hc j s hs.1 bad hb (originalMass j) (hpos j)
      (hhalf j) δ (hbadmass j)).trans hbadbound
  have hagain : ∀ j s, Good j.castSucc s → s.stopped = false →
      (volume : Measure UpperCircular.Circle)
        {d | RefinedUpperRetryFailure.again policy (jobs j) (badEvent j) s d = true} ≤ b := by
    intro j s hs ho
    have hcount : s.accepted.length < k := by rw [hs.2.2.1]; exact j.isLt
    have hprior : ∀ i rec, rec ∈ s.accepted →
        physicalError (fun i => μ (active i))
          (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts rec.first i j ≤
            2 * cellGap (table active reserve cuts) i j ∧
        physicalError (fun i => μ (active i))
          (fun i => (μ (active i)).real (domain reserve.cells)) reserve.cells cuts rec.last i j ≤
            2 * cellGap (table active reserve cuts) i j := by
      intro i rec hrec
      exact ⟨hgood _ (hs.2.2.2 rec hrec).1 i j, hgood _ (hs.2.2.2 rec hrec).2 i j⟩
    have hsub := RefinedUpperCorrectionConditional.good_rejection_subset μ policy hp active hinj
      reserve cuts t eta lam N heta hlam.le hsize selected hc (domain reserve.cells) j s ho
      hs.1 hs.2.1 hcount bad hprior (fun x hx i => hgood x hx i j)
    exact (measure_mono hsub).trans ((RefinedUpperCorrectionProbability.envelope_probability μ
      policy hp hm active reserve cuts t eta lam N heta hlam hN hsmallsize selected hc
      (domain reserve.cells) j s hs.1).trans henvelope)
  have hinit : Good 0 initial := by
    refine ⟨?_, initial_good _ bad⟩
    exact start_safe μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated
      hc.positive hinj (domain reserve.cells) Subset.rfl t eta lam heta hlam.le hc.small hc.sum hmargin
  exact RefinedUpperBatchChance.stopped_probability policy hm jobs badEvent
    (fun j => endpointBad_measurable policy hm (jobs j) bad hb) Good hretry haccept a b B
    hbad hagain hfixed initial hinit rfl

end EnvyFreeResearch.Full.RefinedUpperCorrectionBatchProbability
