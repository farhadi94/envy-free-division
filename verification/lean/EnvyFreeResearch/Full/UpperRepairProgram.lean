import EnvyFreeResearch.Full.UpperRepairAllocationPhysical
import EnvyFreeResearch.Full.UpperRepairRemaining
import EnvyFreeResearch.Full.UpperRepairTrialSuccess

/-! Ordinary-query Repair with actual physical output postprocessing.
Rejection restores the original allocation and buffer while retaining all
new answers. Success returns the assembled recorded allocation and full
buffer complement. Postprocessing issues no oracle queries. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram Chores.QueryProgram
  UpperQueryPrograms ProgramMeasurable

variable {n k q m L : ℕ} [Nonempty (Fin k)]

abbrev PhysicalResult (n k : ℕ) := (Fin k → State n) × State n × Bool

def finish (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (L : ℕ) (theta : I) (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L)
    (r : Result n k q m) : PhysicalResult n k :=
  if r.2.2.2 then (old, ⟨origin.cells, r.2.2.1.history⟩, true)
  else (UpperRepairAllocation.allocation hk chores active origin old r.1 L theta labels pi threshold r.2,
    UpperRepairRemaining.remaining hk active origin r.1 L theta labels pi threshold r.2.2.1, false)

theorem finish_history (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (L : ℕ) (theta : I) (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L)
    (r : Result n k q m) : (finish hk chores active origin old L theta labels pi threshold r).2.1.history = r.2.2.1.history := by
  unfold finish
  split_ifs <;> rfl

theorem finish_stopped (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (L : ℕ) (theta : I) (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L)
    (r : Result n k q m) : (finish hk chores active origin old L theta labels pi threshold r).2.2 = r.2.2.2 := by
  unfold finish
  split_ifs with h
  · exact h.symm
  · exact (Bool.eq_false_iff.mpr h).symm

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (q m L : ℕ) (theta : I) (cap eta lam : ℝ) (p : Tape k q m L) : QProgram n (PhysicalResult n k) :=
  (UpperRepairTrialFull.program hk chores active origin old q m L theta cap eta lam p).bind
    (fun r => .returned (finish hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2 r))

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) : PhysicalResult n k :=
  finish hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2
    (UpperRepairTrialFull.result policy hk chores active origin old q m L theta cap eta lam p)

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) (hn : 1 ≤ n) (hcoarse : k * q ≤ m) (hcorrections : 2 * k ≤ m) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L theta cap eta lam p)
      origin.history (execute policy hk chores active origin old q m L theta cap eta lam p) trace ∧
      (execute policy hk chores active origin old q m L theta cap eta lam p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * m ∧ (trace.map Prod.fst).countP isCut ≤ 3 * m := by
  obtain ⟨trace, he, hh, hq, hc⟩ := UpperRepairTrialFull.program_cost policy hk chores active origin old q m L
    theta cap eta lam p hn hcoarse hcorrections
  refine ⟨trace, ?_, ?_, hq, hc⟩
  · simpa only [program, List.append_nil] using he.bind
      (fun r => Program.returned (finish hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2 r))
      (Executes.returned (execute policy hk chores active origin old q m L theta cap eta lam p) (origin.history ++ trace))
  · exact (finish_history hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2 _).trans hh

section Measurability
variable {X : Type} [MeasurableSpace X]

theorem finish_measurable (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (L : ℕ) (theta : I)
    (labels : X → Labels k q) (pi : X → Equiv.Perm (Fin k)) (threshold : X → Thresholds k L)
    (r : X → Result n k q m) (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hlabels : ∀ c, Measurable (fun x => labels x c)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (hr : Measurable r) :
    Measurable (fun x => finish hk chores active (origin x) (old x) L theta (labels x) (pi x) (threshold x) (r x)) := by
  have hd := measurable_fst.comp hr
  have hs := measurable_snd.comp hr
  have hfinal := measurable_fst.comp (measurable_snd.comp hs)
  have hstopped := measurable_snd.comp (measurable_snd.comp hs)
  have halloc := Measurable.of_eval (UpperRepairAllocation.allocation_measurable hk chores active origin old _
    L theta labels pi threshold _ horigin hold hd hlabels hpi hthreshold hs)
  have hrem := UpperRepairRemaining.remaining_measurable hk active origin _ L theta labels pi threshold _
    horigin hd hlabels hpi hthreshold hfinal
  have hrestore : Measurable (fun x => (⟨(origin x).cells, (r x).2.2.1.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (r x).2.2.1.history))
    exact (state_cells_measurable.comp horigin).prodMk (state_history_measurable.comp hfinal)
  exact ((Measurable.of_eval hold).prodMk (hrestore.prodMk measurable_const)).ite
    (measurableSet_eq_fun hstopped (measurable_const (a := true)))
    (halloc.prodMk (hrem.prodMk measurable_const))

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : X → Tape k q m L) (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L theta cap eta lam (p x)) := by
  have hbase := UpperRepairTrialFull.program_certified hk chores active origin old q m L theta cap eta lam p horigin hold hp
  exact hbase.bind _ (Certified.returned _
    (finish_measurable hk chores active (fun z : X × Result n k q m => origin z.1) (fun z => old z.1)
      L theta (fun z => (p z.1).1) (fun z => (p z.1).2.1.2.1) (fun z => (p z.1).2.1.2.2) Prod.snd
      (horigin.comp measurable_fst) (fun j => (hold j).comp measurable_fst)
      (fun c => (measurable_pi_apply c).comp (measurable_fst.comp (hp.comp measurable_fst)))
      (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp (hp.comp measurable_fst)))))
      (fun j => (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp
        (measurable_fst.comp (measurable_snd.comp (hp.comp measurable_fst)))))) measurable_snd))

end Measurability
end EnvyFreeResearch.Full.UpperRepairProgram
