import EnvyFreeResearch.Full.UpperRepairSuccess
import EnvyFreeResearch.Full.UpperRepairTrialFullProbability

/-! The concrete ordinary-query Repair primitive at the original-population
manuscript scales. Its whole physical output, unconditional rejection budget,
all-attempt query caps and Borel next actions are now instantiated together.
This is a finite primitive, not the unfinished Snapshot/Shrink/global theorem. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperRepair

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairParameters UpperRepairPreparationChecks UpperRepairProgram UpperQueryPrograms
  Chores.QueryProgram ProgramMeasurable

def coarse (n : ℕ) := coarseCount (scale n) (logarithm (scale n))
def fine (n : ℕ) := samples (scale n) (logarithm (scale n))
def repeats (n : ℕ) := repetitions (scale n) (logarithm (scale n))
def reserveMark (n : ℕ) : I :=
  UpperRepairParameters.reserveMark (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))
def cutoff (n : ℕ) := retainedCap (scale n) (logarithm (scale n))
def cellBound (n : ℕ) := fineCap (scale n) (logarithm (scale n))
def gapMultiplier (n : ℕ) := multiplier (scale n)
def nearError (n : ℕ) := oldError (scale n) (logarithm (scale n))

abbrev Tape (n k : ℕ) := UpperRepairTrialLaw.Tape k (coarse n) (fine n) (repeats n)
def law (n k : ℕ) : Measure (Tape n k) := UpperRepairTrialLaw.trialLaw k (coarse n) (fine n) (repeats n)

instance law_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (law n k) := by
  unfold law
  infer_instance

variable {n k : ℕ} [Nonempty (Fin k)]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k) : QProgram n (PhysicalResult n k) :=
  UpperRepairProgram.program hk chores active origin old (coarse n) (fine n) (repeats n)
    (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k) : PhysicalResult n k :=
  UpperRepairProgram.execute policy hk chores active origin old (coarse n) (fine n) (repeats n)
    (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (hinj : Function.Injective active) (origin : State n) (old : Fin k → State n) (p : Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old p) origin.history
      (execute policy hk chores active origin old p) trace ∧
      (execute policy hk chores active origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3 * fine n := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hf := original_population_facts n k hk hkn
  exact UpperRepairProgram.program_cost policy hk chores active origin old (coarse n) (fine n) (repeats n)
    (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p (by omega)
    (by have := hf.logical_grid_budget
        change k * coarseCount (scale n) (logarithm (scale n)) ≤ samples (scale n) (logarithm (scale n))
        omega)
    hf.correction_cut_budget

theorem rejected_restore (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k)
    (hreject : (execute policy hk chores active origin old p).2.2 = true) :
    (execute policy hk chores active origin old p).1 = old ∧
      (execute policy hk chores active origin old p).2.1.cells = origin.cells :=
  UpperRepairProgram.rejected_restore policy hk chores active origin old (coarse n) (fine n) (repeats n)
    (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p hreject

section Physical
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (nearError n))

include hpolicy hinj hgood hpositive hold hnear in
theorem success_facts
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history) (p : Tape n k)
    (hsuccess : (execute policy hk chores active origin old p).2.2 = false) :
    SuccessFacts μ chores active origin old (execute policy hk chores active origin old p) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hf := original_population_facts n k hk hkn
  have hs := scale_large n
  have hell : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  exact UpperRepairProgram.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold
    holdpair holdbuffer holdHistory (coarse n) (fine n) (repeats n) hf.representative_budget
    (reserveMark n) (reserve_positive hs hell) (cutoff n) (cellBound n) (gapMultiplier n) (nearError n)
    (fineCap_positive hs hell).le (multiplier_positive hs).le
    (by have := hf.rounding_margin; change (k : ℝ)^2 ≤ multiplier (scale n); linarith [multiplier_positive hs])
    hf.correction_extra hf.seed_spending (oldError_positive hs hell).le hnear
    hf.normalized_cell_cap hf.total_target_budget p hsuccess

include hpolicy hinj hgood hpositive hold hnear in
theorem failure_lt (hmeas : MeasurablePolicy policy) :
    law n k {p | (execute policy hk chores active origin old p).2.2 = true} < 1 / 64 := by
  have h := UpperRepairTrialFull.original_population_failure_lt μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold hnear
  change UpperRepairTrialLaw.trialLaw k (coarse n) (fine n) (repeats n)
    {p | (UpperRepairProgram.execute policy hk chores active origin old (coarse n) (fine n) (repeats n)
      (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p).2.2 = true} < 1 / 64
  simp_rw [UpperRepairProgram.execute_stopped]
  exact h

end Physical

theorem program_certified {X : Type} [MeasurableSpace X]
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (p : X → Tape n k)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (old x) (p x)) :=
  UpperRepairProgram.program_certified hk chores active origin old (coarse n) (fine n) (repeats n)
    (reserveMark n) (cutoff n) (cellBound n) (gapMultiplier n) p horigin hold hp

theorem measurable_next (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) :
    Measurable (fun z : Tape n k × History n =>
      ((program hk chores active origin old z.1).after z.2).action) :=
  (program_certified hk chores active (fun _ => origin) (fun _ => old) id
    measurable_const (fun _ => measurable_const) measurable_id).measurable_next

end EnvyFreeResearch.Full.UpperRepair
