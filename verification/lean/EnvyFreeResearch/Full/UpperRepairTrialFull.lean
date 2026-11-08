import EnvyFreeResearch.Full.UpperRepairTrialRejection
import EnvyFreeResearch.Full.UpperSnapshotCandidatesGuard

/-! The complete manuscript reserve guard is enforced before returning.
The upper-mass validation is a pure cached final check; its rejection retains
all attempted work and complete answers, so the existing worst-case trace
cap also covers this implementation. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairTrialFull

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQueryPrograms
  UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram UpperRepairTrialRejection
  UpperSnapshotCandidates Chores.QueryProgram ProgramMeasurable

variable {n k q m L : ℕ} [Nonempty (Fin k)]

def finish (active : Fin k → Fin n) (origin : State n) (theta : I) (labels : Labels k q)
    (r : Result n k q m) : Result n k q m :=
  if upperReserve active origin (UpperGridData.reserve r.1 theta labels) theta then r
  else (r.1, (fun _ => []), ⟨origin.cells, r.2.2.1.history⟩, true)

theorem finish_history (active : Fin k → Fin n) (origin : State n) (theta : I) (labels : Labels k q)
    (r : Result n k q m) : (finish active origin theta labels r).2.2.1.history = r.2.2.1.history := by
  unfold finish
  split_ifs <;> rfl

theorem finish_stopped (active : Fin k → Fin n) (origin : State n) (theta : I) (labels : Labels k q)
    (r : Result n k q m) : (finish active origin theta labels r).2.2.2 =
      (r.2.2.2 || !upperReserve active origin (UpperGridData.reserve r.1 theta labels) theta) := by
  by_cases h : upperReserve active origin (UpperGridData.reserve r.1 theta labels) theta = true
  · simp [finish, h]
  · have hf := Bool.eq_false_iff.mpr h
    simp [finish, hf]

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) : QProgram n (Result n k q m) :=
  (UpperRepairTrialProgram.program hk chores active origin old q m L p.2.1.1 theta cap eta lam p.1
    p.2.1.2.1 p.2.1.2.2 p.2.2).bind (fun r => .returned (finish active origin theta p.1 r))

def result (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) : Result n k q m :=
  finish active origin theta p.1
    (UpperRepairTrialRejection.result policy hk chores active origin old q m L theta cap eta lam p)

def Failed (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ) :
    Set (Tape k q m L) :=
  {p | (result policy hk chores active origin old q m L theta cap eta lam p).2.2.2 = true}

theorem grid_result (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) :
    (UpperRepairTrialRejection.result policy hk chores active origin old q m L theta cap eta lam p).1 =
      data policy active origin q p.2.1 := by
  unfold UpperRepairTrialRejection.result UpperRepairTrialProgram.execute executeTrial afterGrid
  split_ifs <;> rfl

theorem failed_eq (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ) :
    Failed policy hk chores active origin old q m L theta cap eta lam =
      UpperRepairTrialRejection.Failed policy hk chores active origin old q m L theta cap eta lam ∪
      {p | upperReserve active origin (UpperGridData.reserve (data policy active origin q p.2.1) theta p.1) theta = false} := by
  ext p
  simp only [Failed, result, Set.mem_setOf_eq, finish_stopped, Bool.or_eq_true,
    Bool.not_eq_true_eq_eq_false, grid_result, mem_union, UpperRepairTrialRejection.Failed]

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) (hn : 1 ≤ n) (hcoarse : k * q ≤ m) (hcorrections : 2 * k ≤ m) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L theta cap eta lam p)
      origin.history (result policy hk chores active origin old q m L theta cap eta lam p) trace ∧
      (result policy hk chores active origin old q m L theta cap eta lam p).2.2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * m ∧ (trace.map Prod.fst).countP isCut ≤ 3 * m := by
  obtain ⟨trace, he, hh, hq, hc⟩ := UpperRepairTrialProgram.program_cost policy hk chores active origin old q m L
    p.2.1.1 theta cap eta lam p.1 p.2.1.2.1 p.2.1.2.2 p.2.2 hn hcoarse hcorrections
  refine ⟨trace, ?_, ?_, hq, hc⟩
  · simpa only [program, List.append_nil] using he.bind
      (fun r => Program.returned (finish active origin theta p.1 r))
      (Executes.returned (result policy hk chores active origin old q m L theta cap eta lam p) (origin.history ++ trace))
  · exact (finish_history active origin theta p.1 _).trans hh

theorem finish_measurable {X : Type} [MeasurableSpace X] (active : Fin k → Fin n)
    (origin : X → State n) (theta : I) (labels : X → Labels k q) (r : X → Result n k q m)
    (horigin : Measurable origin) (hlabels : ∀ c, Measurable (fun x => labels x c)) (hr : Measurable r) :
    Measurable (fun x => finish active (origin x) theta (labels x) (r x)) := by
  have hguard := upperReserve_measurable active origin
    (fun x => UpperGridData.reserve (r x).1 theta (labels x)) theta horigin
    (UpperGridData.reserve_measurable _ theta labels (measurable_fst.comp hr) hlabels)
  have hrestore : Measurable (fun x => (⟨(origin x).cells, (r x).2.2.1.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells, (r x).2.2.1.history))
    exact (state_cells_measurable.comp horigin).prodMk
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hr))))
  exact hr.ite (measurableSet_eq_fun hguard (measurable_const (a := true)))
    ((measurable_fst.comp hr).prodMk (measurable_const.prodMk (hrestore.prodMk measurable_const)))

theorem program_certified {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : X → State n) (old : X → Fin k → State n)
    (q m L : ℕ) (theta : I) (cap eta lam : ℝ) (p : X → Tape k q m L)
    (horigin : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j)) (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L theta cap eta lam (p x)) := by
  have hbase := UpperRepairTrialProgram.program_certified hk chores active origin old q m L
    (fun x => (p x).2.1.1) theta cap eta lam (fun x => (p x).1) (fun x => (p x).2.1.2.1)
    (fun x => (p x).2.1.2.2) (fun x => (p x).2.2) horigin hold
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hp))))
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp hp))
    (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp hp))))
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp hp)))))
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp hp)))
  exact hbase.bind _ (Certified.returned _
    (finish_measurable active (fun z : X × Result n k q m => origin z.1) theta
      (fun z => (p z.1).1) Prod.snd (horigin.comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp (hp.comp measurable_fst))) measurable_snd))

end EnvyFreeResearch.Full.UpperRepairTrialFull
