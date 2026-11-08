import EnvyFreeResearch.Full.NonnegativeMain
import EnvyFreeResearch.Full.RawIntervalPartition
import EnvyFreeResearch.Full.OutputPostprocess

/-!
The nonnegative quantitative lower bound for unsorted raw finite interval
outputs. Incorrect geometry is a failure. A measurable, input-independent
validator turns such returns into query-free nonreturn and preserves the
complete answered transcript and both actual query-cost conventions.
-/

noncomputable section
namespace EnvyFreeResearch.Full.NonnegativeRawMain

open Set MeasureTheory IntervalOracle IntervalAllocation MixedDensity OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativeInputClass NonnegativeRetainedFailure
open NonnegativeSuccess
open scoped Classical ENNReal

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

abbrev RawOutput (n : ℕ) := RawIntervalPartition.Raw (Fin n)

/-- Literal cake/chore comparisons on the physical shares of a raw record. -/
def RawFair (chores : Bool) (rows : Fin n → Row) (r : RawOutput n) : Prop :=
  if chores then
    ∀ i j, (rows i).signedMeasure (RawIntervalPartition.share r i) ≤
      (rows i).signedMeasure (RawIntervalPartition.share r j)
  else
    ∀ i j, (rows i).signedMeasure (RawIntervalPartition.share r j) ≤
      (rows i).signedMeasure (RawIntervalPartition.share r i)

theorem fair_allocation (chores : Bool) (rows : Fin n → Row) (r : RawOutput n)
    (h : RawIntervalPartition.Valid r) :
    Fair chores rows (RawIntervalPartition.allocation r h) ↔ RawFair chores rows r := by
  cases chores <;> rfl

def success (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (flag chores : Bool) (rows : Fin n → Row) : Set Tape :=
  {tape | ∃ fuel r, (run next (flaggedOracle flag (toProfile rows)) tape fuel []).stop = .returned r ∧
    RawIntervalPartition.Valid r ∧ RawFair chores rows r}

def SucceedsOnClass (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (flag chores : Bool) (p : ℝ) : Prop :=
  ∀ rows : Fin n → Row, Admissible rows → ENNReal.ofReal p ≤ μ (success next flag chores rows)

def normalized (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) :
    Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)) :=
  OutputPostprocess.normalized RawIntervalPartition.decode next

theorem normalized_measurable (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2)) :
    Measurable (fun z : Tape × History (Query (Fin n)) Reply => normalized next z.1 z.2) :=
  OutputPostprocess.normalized_measurable RawIntervalPartition.decode
    RawIntervalPartition.decode_measurable next hnext

omit [MeasurableSpace Tape] in
/-- Correct raw returns and correct normalized returns are exactly the same
tape event. Validity is geometric; no valuation-dependent repair is used. -/
theorem normalized_success (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (flag chores : Bool) (rows : Fin n → Row) :
    eventualSuccess (normalized next) (flaggedOracle flag (toProfile rows)) []
      {A | Fair chores rows A} = success next flag chores rows := by
  ext tape
  constructor
  · rintro ⟨fuel, A, hreturned, hfair⟩
    obtain ⟨r, hr, hd⟩ := (OutputPostprocess.returned_normalized_iff
      RawIntervalPartition.decode next (flaggedOracle flag (toProfile rows)) tape fuel [] A).mp hreturned
    obtain ⟨hvalid, rfl⟩ := (RawIntervalPartition.decode_some_iff r A).mp hd
    exact ⟨fuel, r, hr, hvalid, (fair_allocation chores rows r hvalid).mp hfair⟩
  · rintro ⟨fuel, r, hr, hvalid, hfair⟩
    refine ⟨fuel, RawIntervalPartition.allocation r hvalid, ?_,
      (fair_allocation chores rows r hvalid).mpr hfair⟩
    exact (OutputPostprocess.returned_normalized_iff RawIntervalPartition.decode next
      (flaggedOracle flag (toProfile rows)) tape fuel [] _).mpr
        ⟨r, hr, (RawIntervalPartition.decode_some_iff _ _).mpr ⟨hvalid, rfl⟩⟩

omit [MeasurableSpace Tape] in
theorem malformed_return_diverges (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (oracle : Query (Fin n) → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History (Query (Fin n)) Reply) (r : RawOutput n)
    (hr : (run next oracle tape fuel history).stop = .returned r)
    (hbad : ¬ RawIntervalPartition.Valid r) :
    (run (normalized next) oracle tape fuel history).stop = .diverged := by
  have hd := (RawIntervalPartition.decode_none_iff r).mpr hbad
  simp only [normalized, OutputPostprocess.run_normalized, OutputPostprocess.execution,
    hr, OutputPostprocess.stop, hd]

omit [MeasurableSpace Tape] in
theorem malformed_return_failure (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (flag chores : Bool) (rows : Fin n → Row) (tape : Tape) (fuel : ℕ) (r : RawOutput n)
    (hr : (run next (flaggedOracle flag (toProfile rows)) tape fuel []).stop = .returned r)
    (hbad : ¬ RawIntervalPartition.Valid r) : tape ∉ success next flag chores rows := by
  rw [← normalized_success]
  have hdiv := malformed_return_diverges next (flaggedOracle flag (toProfile rows)) tape fuel [] r hr hbad
  apply terminal_failure_no_eventual_success (normalized next)
    (flaggedOracle flag (toProfile rows)) tape [] {A | Fair chores rows A} fuel
  · intro query hquery
    rw [hdiv] at hquery
    cases hquery
  · rintro ⟨A, hreturned, _⟩
    rw [hdiv] at hreturned
    cases hreturned

theorem normalized_succeeds (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag chores : Bool) (p : ℝ)
    (h : SucceedsOnClass μ next flag chores p) :
    NonnegativeMain.SucceedsOnClass μ (normalized next) flag chores p := by
  intro rows hrows
  simpa only [normalized_success] using h rows hrows

def expectedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag : Bool) : ℝ≥0∞ :=
  ∫⁻ tape, (queryCost next (flaggedOracle flag uniform) tape [] : ℝ≥0∞) ∂μ

def expectedAttemptedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag : Bool) : ℝ≥0∞ :=
  ∫⁻ tape, (AttemptedQueries.attemptedCost next (flaggedOracle flag uniform) tape [] : ℝ≥0∞) ∂μ

omit [MeasurableSpace Tape] in
/-- Validation preserves the actual answered-query cost pointwise, including
infinite querying and finite-query failure or nonreturn. -/
theorem answeredCost_normalized (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (oracle : Query (Fin n) → Option Reply) (tape : Tape) (history : History (Query (Fin n)) Reply) :
    queryCost (normalized next) oracle tape history = queryCost next oracle tape history :=
  OutputPostprocess.queryCost_normalized RawIntervalPartition.decode next oracle tape history

omit [MeasurableSpace Tape] in
theorem attemptedCost_normalized (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (oracle : Query (Fin n) → Option Reply) (tape : Tape) (history : History (Query (Fin n)) Reply) :
    AttemptedQueries.attemptedCost (normalized next) oracle tape history =
      AttemptedQueries.attemptedCost next oracle tape history :=
  OutputPostprocess.attemptedCost_normalized RawIntervalPartition.decode next oracle tape history

theorem expectedCost_normalized (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag : Bool) :
    NonnegativeHardFamily.expectedCost μ (normalized next) flag = expectedCost μ next flag := by
  simp only [NonnegativeHardFamily.expectedCost, expectedCost, answeredCost_normalized]

omit [MeasurableSpace Tape] in
/-- The nonnegative endpoint's determining-list convention is exactly the
shared attempted-query count, including the possible terminal illegal call. -/
theorem main_attemptedCost_eq
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) (tape : Tape) :
    NonnegativeMain.attemptedCost next flag tape =
      AttemptedQueries.attemptedCost next (flaggedOracle flag uniform) tape [] := by
  unfold NonnegativeMain.attemptedCost AttemptedQueries.attemptedCost
  apply iSup_congr
  intro fuel
  rw [determiningRequests_length]
  rfl

theorem expectedAttemptedCost_normalized (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag : Bool) :
    NonnegativeMain.expectedAttemptedCost μ (normalized next) flag = expectedAttemptedCost μ next flag := by
  simp only [NonnegativeMain.expectedAttemptedCost, expectedAttemptedCost,
    main_attemptedCost_eq, attemptedCost_normalized]

theorem expectedCost_le_expectedAttemptedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n)) (flag : Bool) :
    expectedCost μ next flag ≤ expectedAttemptedCost μ next flag := by
  apply lintegral_mono
  intro tape
  exact ENat.toENNReal_mono (AttemptedQueries.queryCost_le_attemptedCost
    next (flaggedOracle flag uniform) tape [])

theorem all_windows (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    ENNReal.ofReal ((((n : ℝ) * p - 1) / w) - ((n : ℝ) - 1) / (2 * (n : ℝ) * w ^ 2)) ≤
      expectedCost μ next flag := by
  have h := NonnegativeMain.all_windows μ hn (normalized next) (normalized_measurable next hnext)
    flag chores p hp hp1 (normalized_succeeds μ next flag chores p hprotocol) w hw hwsmall
  simpa only [expectedCost_normalized] using h

theorem optimized (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p) :
    ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1))) ≤
      expectedCost μ next flag := by
  have h := NonnegativeMain.optimized μ hn (normalized next) (normalized_measurable next hnext)
    flag chores p hp hp1 (normalized_succeeds μ next flag chores p hprotocol) hthreshold
  simpa only [expectedCost_normalized] using h

theorem quadratic (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p) (hlarge : 3 ≤ (n : ℝ) * p) :
    0 < p ^ 2 / 8 ∧
      ENNReal.ofReal ((p ^ 2 / 8) * (n : ℝ) ^ 2) ≤ expectedCost μ next flag := by
  have h := NonnegativeMain.quadratic μ hn (normalized next) (normalized_measurable next hnext)
    flag chores p hp hp1 (normalized_succeeds μ next flag chores p hprotocol) hlarge
  simpa only [expectedCost_normalized] using h

theorem two_thirds (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 4 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (hprotocol : SucceedsOnClass μ next flag chores (2 / 3)) :
    ENNReal.ofReal ((n : ℝ) * (2 * (n : ℝ) - 3) ^ 2 / (18 * ((n : ℝ) - 1))) ≤
      expectedCost μ next flag := by
  have h := NonnegativeMain.two_thirds μ hn (normalized next) (normalized_measurable next hnext)
    flag chores (normalized_succeeds μ next flag chores (2 / 3) hprotocol)
  simpa only [expectedCost_normalized] using h

theorem all_windows_attempted (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    ENNReal.ofReal ((((n : ℝ) * p - 1) / w) - ((n : ℝ) - 1) / (2 * (n : ℝ) * w ^ 2)) ≤
      expectedAttemptedCost μ next flag :=
  (all_windows μ hn next hnext flag chores p hp hp1 hprotocol w hw hwsmall).trans
    (expectedCost_le_expectedAttemptedCost μ next flag)

theorem optimized_attempted (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p) :
    ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1))) ≤
      expectedAttemptedCost μ next flag :=
  (optimized μ hn next hnext flag chores p hp hp1 hprotocol hthreshold).trans
    (expectedCost_le_expectedAttemptedCost μ next flag)

end EnvyFreeResearch.Full.NonnegativeRawMain

#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.normalized_success
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.malformed_return_failure
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.answeredCost_normalized
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.attemptedCost_normalized
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.all_windows
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.optimized
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.quadratic
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.two_thirds
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.all_windows_attempted
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.optimized_attempted
