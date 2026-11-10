import EnvyFreeResearch.Full.RefinedUpperRepairProgram
import EnvyFreeResearch.Full.UpperRepairTrialLaw

/-! The original independent random tape for the refined physical Repair.
Sampler-owner/target pairs are retained; the law is not conditioned on any
preparation, assignment or correction event. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairLaw
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation ProgramMeasurable

abbrev Parameter (k m L : ℕ) := UpperRepairTrialLaw.Parameter k m L
abbrev Tape (k m L r : ℕ) := Parameter k m L × (Fin k → Fin r → UpperCircular.Circle)

def retryLaw (k r : ℕ) : Measure (Fin k → Fin r → UpperCircular.Circle) :=
  Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin r => (volume : Measure UpperCircular.Circle)))
instance retryLaw_probability (k r : ℕ) : IsProbabilityMeasure (retryLaw k r) := by
  unfold retryLaw
  infer_instance

def trialLaw (k m L r : ℕ) : Measure (Tape k m L r) :=
  (UpperRepairTrialLaw.parameterLaw k m L).prod (retryLaw k r)
instance trialLaw_probability {k m L r : ℕ} [Nonempty (Fin k)] :
    IsProbabilityMeasure (trialLaw k m L r) := by
  unfold trialLaw
  infer_instance

variable {n k m L r : ℕ} [Nonempty (Fin k)]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (eta lam : ℝ) (p : Tape k m L r) :=
  RefinedUpperRepairProgram.program hk chores active origin old q m L p.1.1 p.1.2.1 p.1.2.2 eta lam p.2

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q : ℕ) (eta lam : ℝ) (p : Tape k m L r) :=
  RefinedUpperRepairProgram.execute policy hk chores active origin old q m L p.1.1 p.1.2.1 p.1.2.2 eta lam p.2

theorem original_samples_law
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q : ℕ) :
    MeasurePreserving (fun x : Tape k m L r =>
      (UpperGridMerge.prepare policy active origin q m x.1.1).2.1)
      (trialLaw k m L r) (Measure.pi (fun _ : Fin m => UpperMixtureSampling.mixture μ active origin.cells)) :=
  (UpperRepairTrialLaw.original_samples_law μ policy hpolicy hmeas active origin hgood hpositive q).comp
    measurePreserving_fst

variable {X : Type} [MeasurableSpace X]

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q : ℕ) (eta lam : ℝ)
    (p : X → Tape k m L r) (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (old x) q eta lam (p x)) := by
  have hparam := measurable_fst.comp hp
  have hdraw := measurable_fst.comp hparam
  have hi := measurable_snd.comp hparam
  exact RefinedUpperRepairProgram.program_certified hk chores active origin old q m L
    (fun x => (p x).1.1) (fun x => (p x).1.2.1) (fun x => (p x).1.2.2) eta lam (fun x => (p x).2)
    ho hold (fun e => (measurable_pi_apply e).comp hdraw) (measurable_fst.comp hi)
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp hi))
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp hp))

end EnvyFreeResearch.Full.RefinedUpperRepairLaw
