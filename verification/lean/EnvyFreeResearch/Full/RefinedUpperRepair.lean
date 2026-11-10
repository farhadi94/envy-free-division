import EnvyFreeResearch.Full.RefinedUpperRepairSuccess
import EnvyFreeResearch.Full.RefinedUpperRepairParameters
import EnvyFreeResearch.Full.RefinedUpperRepairOutputMeasurable

/-! Concrete ordinary-query Repair at the original-population revised scales.
This facade binds physical correctness, all-attempt cost, and Borel behavior.
The unconditional rejection estimate is assembled separately. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperParameterCounts RefinedUpperRepairParameters RefinedUpperRepairProgram
  UpperQueryPrograms Chores.QueryProgram ProgramMeasurable
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale)

def coarse (n : ℕ) := coarseCount (scale n) (logarithm (scale n))
def fine (n : ℕ) := samples (scale n) (logarithm (scale n))
def repeats (n : ℕ) := repetitions (scale n) (logarithm (scale n))
def retries (n : ℕ) := logarithm (scale n)
def cellBound (n : ℕ) := fineCap (scale n) (logarithm (scale n))
def gapMultiplier (n : ℕ) := multiplier (scale n)
def nearError (n : ℕ) := oldError (scale n)

abbrev Tape (n k : ℕ) := RefinedUpperRepairLaw.Tape k (fine n) (repeats n) (retries n)
def law (n k : ℕ) : Measure (Tape n k) := RefinedUpperRepairLaw.trialLaw k (fine n) (repeats n) (retries n)
instance law_probability {n k : ℕ} [Nonempty (Fin k)] : IsProbabilityMeasure (law n k) := by
  unfold law
  infer_instance
variable {n k : ℕ} [Nonempty (Fin k)]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k) : QProgram n (PhysicalResult n k) :=
  RefinedUpperRepairLaw.program hk chores active origin old (coarse n) (cellBound n) (gapMultiplier n) p

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k) : PhysicalResult n k :=
  RefinedUpperRepairLaw.execute policy hk chores active origin old (coarse n) (cellBound n) (gapMultiplier n) p

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (hinj : Function.Injective active) (origin : State n) (old : Fin k → State n) (p : Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old p) origin.history
      (execute policy hk chores active origin old p) trace ∧
      (execute policy hk chores active origin old p).2.1.history=origin.history++trace ∧
      trace.length ≤ 6*n*fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3*fine n := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have hs1 : 1 ≤ scale n := by exact_mod_cast (show (1 : ℝ) ≤ scale n from (by norm_num : (1 : ℝ) ≤ 2^42).trans hs)
  have hk256 : 256*k ≤ scale n := by
    have h := active_scale n k hkn
    exact_mod_cast (show (256 : ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact program_cost_linear policy hk chores active origin old (coarse n) (fine n) (repeats n)
    p.1.1 p.1.2.1 p.1.2.2 (cellBound n) (gapMultiplier n) p.2 (by omega)
    (by have h := (original_count_facts n k hk hkn).1; change k*coarseCount _ _ ≤ samples _ _; omega)
    (correction_retries_fit hs1 hk256)

theorem rejected_restore (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (p : Tape n k)
    (hr : (execute policy hk chores active origin old p).2.2=true) :
    (execute policy hk chores active origin old p).1=old ∧
      (execute policy hk chores active origin old p).2.1.cells=origin.cells :=
  RefinedUpperRepairProgram.rejected_restore policy hk chores active origin old (coarse n) (fine n) (repeats n)
    p.1.1 p.1.2.1 p.1.2.2 (cellBound n) (gapMultiplier n) p.2 hr

theorem success_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : UpperRepairPreparationChecks.Near chores μ active origin old (nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history⊆origin.history) (p : Tape n k)
    (hsuccess : (execute policy hk chores active origin old p).2.2=false) :
    SuccessFacts μ chores active origin old (execute policy hk chores active origin old p) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have ha := active_scale n k hkn
  have hs256 : 256 ≤ scale n := by exact_mod_cast (show (256 : ℝ) ≤ scale n by exact (by norm_num : (256 : ℝ) ≤ 2^42).trans hs)
  have hk256 : 256*k ≤ scale n := by exact_mod_cast (show (256 : ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact RefinedUpperRepairProgram.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold
    holdpair holdbuffer holdHistory (coarse n) (fine n) (repeats n) (parent_budget hs he ha)
    (2*(fine n : ℝ)) (cellBound n) (gapMultiplier n) (nearError n)
    (by unfold cellBound fineCap; positivity) (by unfold gapMultiplier multiplier; positivity)
    (linear_margin hs ha) (correction_spending hs he ha) (seed_spending hs he ha)
    (by unfold nearError oldError; positivity) hnear (cell_cap hs he) (target_total hs he ha)
    (by exact_mod_cast cell_count hs256 (logarithm_positive hs) hk256 (by omega))
    p.1.1 p.1.2.1 p.1.2.2 p.2 hsuccess

theorem program_certified {X : Type} [MeasurableSpace X]
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (p : X → Tape n k)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (old x) (p x)) :=
  RefinedUpperRepairLaw.program_certified hk chores active origin old (coarse n) (cellBound n) (gapMultiplier n) p ho hold hp

theorem execute_measurable {X : Type} [MeasurableSpace X]
    (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (p : X → Tape n k)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Measurable (fun x => execute policy hk chores active (origin x) (old x) (p x)) :=
  RefinedUpperRepairOutputMeasurable.execute_measurable policy hmeas hk chores active origin old
    (coarse n) (cellBound n) (gapMultiplier n) p ho hold hp

end EnvyFreeResearch.Full.RefinedUpperRepair
