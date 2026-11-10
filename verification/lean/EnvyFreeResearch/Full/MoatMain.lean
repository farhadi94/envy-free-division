import EnvyFreeResearch.Full.MoatLower
import EnvyFreeResearch.Full.NonnegativeRawMain

/-! Stronger nonnegative lower bound, with the unchanged public input,
protocol, and raw finite-output models. Only fixed-input correctness and
measurability are hypotheses; the expectation is unconditional. -/
namespace EnvyFreeResearch.Full.MoatMain
open MeasureTheory IntervalOracle IntervalAllocation OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRetainedFailure
open scoped ENNReal

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

theorem normalized (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hprotocol : NonnegativeMain.SucceedsOnClass μ next flag chores p) :
    ENNReal.ofReal (max ((n:ℝ)*((n:ℝ)*p-1)/2) ((n:ℝ)^2*p/4-1)) ≤
      NonnegativeHardFamily.expectedCost μ next flag := by
  apply MoatLower.physical_family μ hn next hnext flag chores p hp0 hp1
  intro two w h hw hw1 hh hhw z
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hw0 : 0 < w := lt_trans (by positivity) hw
  exact hprotocol (MoatExperiment.rows two chores w h z)
    (MoatFamily.admissible chores hw0 hw1.le hh.le hhw (MoatSelection.toFamily two z))

/-- Main end-to-end statement, including arbitrary finite unsorted output
intervals, malformed outputs, illegal requests, and divergent executions.
`ofReal` also takes the maximum with zero. -/
theorem raw (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (NonnegativeRawMain.RawOutput n))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hprotocol : NonnegativeRawMain.SucceedsOnClass μ next flag chores p) :
    ENNReal.ofReal (max ((n:ℝ)*((n:ℝ)*p-1)/2) ((n:ℝ)^2*p/4-1)) ≤
      NonnegativeRawMain.expectedCost μ next flag := by
  have h := normalized μ hn (NonnegativeRawMain.normalized next)
    (NonnegativeRawMain.normalized_measurable next hnext) flag chores p hp0 hp1
    (NonnegativeRawMain.normalized_succeeds μ next flag chores p hprotocol)
  simpa only [NonnegativeRawMain.expectedCost_normalized] using h

end EnvyFreeResearch.Full.MoatMain

#print axioms EnvyFreeResearch.Full.MoatMain.normalized
#print axioms EnvyFreeResearch.Full.MoatMain.raw
