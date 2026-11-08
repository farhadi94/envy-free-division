import EnvyFreeResearch.Full.NonnegativeInputClass

/-!
# The full randomized exact nonnegative lower bound

The tape is an arbitrary probability space. The single measurable protocol
receives input information only through actual Eval/Cut replies. Its returned
allocation has a finite number of arbitrary real interval endpoints, without
a uniform component bound or an expected component-count assumption.

Every bound concerns the unconditional extended expectation of answered
queries on the uniform profile. `flag = true` counts unavailable-target
answers; `flag = false` permits an uncounted illegal terminal request.
Finite-call divergence and infinite query cost are included.
-/

namespace EnvyFreeResearch.Full.NonnegativeMain

open MeasureTheory IntervalOracle IntervalAllocation MixedDensity OracleProtocol
open NonnegativeOracle NonnegativeSuccess NonnegativeExperiment NonnegativeRetainedFailure
open NonnegativeInputClass NonnegativeHardFamily
open scoped ENNReal

variable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]

/-- The manuscript's fixed-input success hypothesis, stated only in terms
of the public input class and actual legal finite correct returns. -/
def SucceedsOnClass (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag chores : Bool) (p : ℝ) : Prop :=
  ∀ rows : Fin n → Row, Admissible rows → ENNReal.ofReal p ≤
    μ (eventualSuccess next (flaggedOracle flag (toProfile rows)) [] {A | Fair chores rows A})

theorem hard_family_guarantee (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag chores : Bool) (p : ℝ) (hprotocol : SucceedsOnClass μ next flag chores p)
    (h : ℝ) (_hh0 : 0 < h) (hh1 : h < 1) (input : Input n) :
    ENNReal.ofReal p ≤ μ (eventualSuccess next (inputOracle flag h input) []
      {A | Fair chores (inputRows h input) A}) :=
  hprotocol (inputRows h input) (inputRows_admissible h input hh1)

/-- The all-window conclusion of Theorem 2.3, already on normalized
finite-step densities in the public window [1/2,3/2]. `ofReal` takes the
maximum with zero, so the statement also covers negative displayed bounds. -/
theorem all_windows (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    ENNReal.ofReal ((((n : ℝ) * p - 1) / w) - ((n : ℝ) - 1) / (2 * (n : ℝ) * w ^ 2)) ≤
      expectedCost μ next flag := by
  have hbound := NonnegativeLower.all_windows μ hn next hnext flag chores p hp.le hp1
    (hard_family_guarantee μ next flag chores p hprotocol) w hw hwsmall
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hformula : R8Lower.retainedQueryLower n p w =
      (((n : ℝ) * p - 1) / w) - ((n : ℝ) - 1) / (2 * (n : ℝ) * w ^ 2) := by
    unfold R8Lower.retainedQueryLower R8Lower.decoderFactor
    field_simp
    ring
  simpa only [hformula] using hbound

/-- The explicit optimized bound requested in Theorem 2.3. Its threshold
is equivalent to legality of the optimizing window for n >= 2. -/
theorem optimized (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p) :
    ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1))) ≤
      expectedCost μ next flag :=
  NonnegativeLower.optimized μ hn next hnext flag chores p hp.le hp1
    (hard_family_guarantee μ next flag chores p hprotocol) hthreshold

/-- An explicit Omega_p(n^2) certificate: for every fixed p > 0, the
constant p^2/8 is positive and applies to all n with np >= 3. -/
theorem quadratic (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p) (hlarge : 3 ≤ (n : ℝ) * p) :
    0 < p ^ 2 / 8 ∧
      ENNReal.ofReal ((p ^ 2 / 8) * (n : ℝ) ^ 2) ≤ expectedCost μ next flag := by
  have hnr2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p := by
    have hdiv : 0 ≤ 2 / (n : ℝ) := by positivity
    linarith
  have hoptimized := optimized μ hn next hnext flag chores p hp hp1 hprotocol hthreshold
  have hsquare : ((n : ℝ) * p) ^ 2 / 4 ≤ ((n : ℝ) * p - 1) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) * p - 2)]
  have hmult := mul_le_mul_of_nonneg_left hsquare hnr.le
  have hconstant : (p ^ 2 / 8) * (n : ℝ) ^ 2 ≤
      (n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1)) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * ((n : ℝ) - 1))).mpr
    nlinarith [sq_nonneg ((n : ℝ) * p)]
  exact ⟨by positivity, (ENNReal.ofReal_le_ofReal hconstant).trans hoptimized⟩

/-- The manuscript's displayed specialization at success probability 2/3. -/
theorem two_thirds (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 4 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (hprotocol : SucceedsOnClass μ next flag chores (2 / 3)) :
    ENNReal.ofReal ((n : ℝ) * (2 * (n : ℝ) - 3) ^ 2 / (18 * ((n : ℝ) - 1))) ≤
      expectedCost μ next flag := by
  have hnr4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * (2 / 3) := by
    have hdiv : 3 - (n : ℝ) * (2 / 3) ≤ 2 / (n : ℝ) := by
      apply (le_div_iff₀ hnr).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hnr4)
        (show 0 ≤ 2 * (n : ℝ) - 1 by linarith)]
    linarith
  have hbound := optimized μ (by omega) next hnext flag chores (2 / 3)
    (by norm_num) (by norm_num) hprotocol hthreshold
  have hformula : (n : ℝ) * ((n : ℝ) * (2 / 3) - 1) ^ 2 / (2 * ((n : ℝ) - 1)) =
      (n : ℝ) * (2 * (n : ℝ) - 3) ^ 2 / (18 * ((n : ℝ) - 1)) := by
    have hne : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  simpa only [hformula] using hbound

/-- Attempted calls include the one possible terminal illegal call. A cap's
pending request is not counted until the oracle is actually consulted. -/
noncomputable def attemptedCost
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (tape : Tape) : ℕ∞ :=
  ⨆ fuel : ℕ, ((determiningRequests
    (run next (flaggedOracle flag NonnegativeProfile.uniform) tape fuel [])).length : ℕ∞)

noncomputable def expectedAttemptedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) : ℝ≥0∞ :=
  ∫⁻ tape, (attemptedCost next flag tape : ℝ≥0∞) ∂μ

theorem expectedCost_le_expectedAttemptedCost (μ : Measure Tape)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) :
    expectedCost μ next flag ≤ expectedAttemptedCost μ next flag := by
  apply lintegral_mono
  intro tape
  apply ENat.toENNReal_mono
  apply iSup_le
  intro fuel
  have hlen : (run next (flaggedOracle flag NonnegativeProfile.uniform) tape fuel []).answered.length ≤
      (determiningRequests (run next (flaggedOracle flag NonnegativeProfile.uniform)
        tape fuel [])).length := by
    rw [determiningRequests_length]
    omega
  exact (show ((run next (flaggedOracle flag NonnegativeProfile.uniform)
      tape fuel []).answered.length : ℕ∞) ≤
      ((determiningRequests (run next (flaggedOracle flag NonnegativeProfile.uniform)
        tape fuel [])).length : ℕ∞) by exact_mod_cast hlen).trans
    (le_iSup (fun k : ℕ => ((determiningRequests
      (run next (flaggedOracle flag NonnegativeProfile.uniform) tape k [])).length : ℕ∞)) fuel)

theorem optimized_attempted (μ : Measure Tape) [IsProbabilityMeasure μ] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag chores : Bool) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hprotocol : SucceedsOnClass μ next flag chores p)
    (hthreshold : 3 - 2 / (n : ℝ) ≤ (n : ℝ) * p) :
    ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * p - 1) ^ 2 / (2 * ((n : ℝ) - 1))) ≤
      expectedAttemptedCost μ next flag :=
  (optimized μ hn next hnext flag chores p hp hp1 hprotocol hthreshold).trans
    (expectedCost_le_expectedAttemptedCost μ next flag)

end EnvyFreeResearch.Full.NonnegativeMain

#print axioms EnvyFreeResearch.Full.NonnegativeMain.all_windows
#print axioms EnvyFreeResearch.Full.NonnegativeMain.optimized
#print axioms EnvyFreeResearch.Full.NonnegativeMain.quadratic
#print axioms EnvyFreeResearch.Full.NonnegativeMain.two_thirds
#print axioms EnvyFreeResearch.Full.NonnegativeMain.optimized_attempted
