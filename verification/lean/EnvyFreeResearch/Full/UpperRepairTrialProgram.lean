import EnvyFreeResearch.Full.UpperPreparedTrialProgramMeasurable
import EnvyFreeResearch.Full.UpperPreparedTrialCost
import EnvyFreeResearch.Full.UpperGridDataMeasurable
import EnvyFreeResearch.Full.UpperLogicalIsolation

/-! The actual preparation/isolation/correction trial, with no assumed
target or acceptance computation. Every post-grid operation reads returned
caches and finite fresh randomness. Physical package joining is subsequent
pure postprocessing and is not claimed by this compiler module. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairTrialProgram

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperCircularStage
  UpperQueryPrograms UpperCorrectionExecution UpperPreparedTrialProgram
  UpperLogicalIsolation UpperRepairJobs

variable {n k q m L : ℕ} [Nonempty (Fin k)]

abbrev Labels (k q : ℕ) := Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + 1) → I
abbrev Thresholds (k L : ℕ) := Fin (jobCount k - 1 + 1) → Fin (L + 1)

def approved (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : Grid n k q m) (L : ℕ)
    (theta : I) (cap lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) : Bool :=
  UpperGridData.guard active origin data (requests k L) theta cap labels &&
    !(cycleReject chores (dataMatrix hk active origin old data L theta labels pi threshold)
      (dataDisagreement active data theta labels) lam)

theorem approved_iff (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : Grid n k q m) (L : ℕ)
    (theta : I) (cap lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) :
    approved hk chores active origin old data L theta cap lam labels pi threshold = true ↔
      UpperGridData.guard active origin data (requests k L) theta cap labels = true ∧
      cycleReject chores (dataMatrix hk active origin old data L theta labels pi threshold)
        (dataDisagreement active data theta labels) lam = false := by
  simp only [approved, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (cap eta lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) (starts : Fin k → UpperCircular.Circle) :
    QProgram n (Result n k q m) :=
  UpperPreparedTrialProgram.program active origin q m draw theta labels eta lam
    (fun data => dataTargets hk q chores active origin old data L theta labels pi threshold lam)
    (fun data => approved hk chores active origin old data L theta cap lam labels pi threshold) starts

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (cap eta lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) (starts : Fin k → UpperCircular.Circle) : Result n k q m :=
  executeTrial policy active origin q m draw theta labels eta lam
    (fun data => dataTargets hk q chores active origin old data L theta labels pi threshold lam)
    (fun data => approved hk chores active origin old data L theta cap lam labels pi threshold) starts

theorem program_executes (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (cap eta lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) (starts : Fin k → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy)
      (program hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts) origin.history
      (execute policy hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts) trace ∧
      (execute policy hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts).2.2.1.history =
        origin.history ++ trace ∧ trace.length ≤ (k * q + m) * (n + 1) + k * (2 * (n + 1)) ∧
      (trace.map Prod.fst).countP isCut ≤ k * q + m + 2 * k :=
  UpperPreparedTrialProgram.program_executes policy active origin q m draw theta labels eta lam _ _ starts

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (cap eta lam : ℝ) (labels : Labels k q) (pi : Equiv.Perm (Fin k))
    (threshold : Thresholds k L) (starts : Fin k → UpperCircular.Circle)
    (hn : 1 ≤ n) (hcoarse : k * q ≤ m) (hcorrections : 2 * k ≤ m) :
    ∃ trace, Executes (totalPolicy policy)
      (program hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts) origin.history
      (execute policy hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts) trace ∧
      (execute policy hk chores active origin old q m L draw theta cap eta lam labels pi threshold starts).2.2.1.history =
        origin.history ++ trace ∧ trace.length ≤ 6 * n * m ∧ (trace.map Prod.fst).countP isCut ≤ 3 * m :=
  UpperPreparedTrialCost.raw_trial_bounds policy active origin q m draw theta labels eta lam _ _ starts hn hcoarse hcorrections

section Measurability

variable {X : Type} [MeasurableSpace X]

theorem approved_measurable (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → Grid n k q m) (L : ℕ)
    (theta : I) (cap lam : ℝ) (labels : X → Labels k q) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Thresholds k L)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hdata : Measurable data)
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) :
    Measurable (fun x => approved hk chores active (origin x) (old x) (data x)
      L theta cap lam (labels x) (pi x) (threshold x)) := by
  have hg := UpperGridData.guard_measurable active origin data (requests k L) theta
    (fun _ => cap) labels horigin hdata measurable_const hlabels
  have hV := dataMatrix_measurable hk active origin old data L theta labels pi threshold
    horigin hold hdata hlabels hpi hthreshold
  have hA := dataDisagreement_measurable active data theta labels hdata hlabels
  have hc := cycleReject_measurable chores _ _ lam hV hA
  exact (measurable_of_countable (fun p : Bool × Bool => p.1 && !p.2)).comp (hg.prodMk hc)

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ) (draw : X → Fin m → Fin k × I)
    (theta : I) (cap eta lam : ℝ) (labels : X → Labels k q) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Thresholds k L) (starts : X → Fin k → UpperCircular.Circle)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hdraw : ∀ j, Measurable (fun x => draw x j))
    (hlabels : ∀ p, Measurable (fun x => labels x p)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j))
    (hstarts : ∀ j, Measurable (fun x => starts x j)) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L (draw x)
      theta cap eta lam (labels x) (pi x) (threshold x) (starts x)) := by
  apply UpperPreparedTrialProgramMeasurable.program_certified active origin q m draw theta labels
    (fun _ => eta) (fun _ => lam) _ _ starts horigin hdraw hlabels measurable_const measurable_const
  · intro i
    exact dataTargets_measurable hk q chores active (fun z : X × Grid n k q m => origin z.1)
      (fun z => old z.1) (fun z => z.2) L theta (fun z => labels z.1) (fun z => pi z.1)
      (fun z => threshold z.1) lam (horigin.comp measurable_fst) (fun j => (hold j).comp measurable_fst)
      measurable_snd (fun p => (hlabels p).comp measurable_fst) (hpi.comp measurable_fst)
      (fun j => (hthreshold j).comp measurable_fst) i
  · exact approved_measurable hk chores active (fun z : X × Grid n k q m => origin z.1)
      (fun z => old z.1) (fun z => z.2) L theta cap lam (fun z => labels z.1) (fun z => pi z.1)
      (fun z => threshold z.1) (horigin.comp measurable_fst) (fun j => (hold j).comp measurable_fst)
      measurable_snd (fun p => (hlabels p).comp measurable_fst) (hpi.comp measurable_fst)
      (fun j => (hthreshold j).comp measurable_fst)
  · exact hstarts

end Measurability

end EnvyFreeResearch.Full.UpperRepairTrialProgram
