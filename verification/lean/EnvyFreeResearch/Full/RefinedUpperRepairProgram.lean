import EnvyFreeResearch.Full.RefinedUpperRepairAssembly
import EnvyFreeResearch.Full.RefinedUpperRepairAllocation
import EnvyFreeResearch.Full.RefinedUpperRepairRemaining

/-! Complete ordinary-query Repair with physical output and full-buffer
reconstruction. Rejection restores all input material and retains every
answered query. No output postprocessing invokes the oracle. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairProgram
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairJobs UpperQueryPrograms Chores.QueryProgram ProgramMeasurable RefinedUpperPreparationProgram
variable {n k coarse fine r : ℕ} [Nonempty (Fin k)]
abbrev PhysicalResult (n k : ℕ) := (Fin k → State n) × State n × Bool

def finish (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) : PhysicalResult n k :=
  if result.2.stopped then (old,⟨origin.cells,result.2.current.history⟩,true)
  else (RefinedUpperRepairAllocation.allocation hk chores active origin old result.1.1 L pi threshold
      (RefinedUpperRepairAssembly.stage chores active eta lam result),
    RefinedUpperRepairRemaining.remaining hk active origin result.1.1 L pi threshold result.2.current,false)

theorem finish_history (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) :
    (finish hk chores active origin old L pi threshold eta lam result).2.1.history = result.2.current.history := by
  unfold finish
  split_ifs <;> rfl

theorem finish_stopped (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) :
    (finish hk chores active origin old L pi threshold eta lam result).2.2 = result.2.stopped := by
  unfold finish
  split_ifs with h
  · exact h.symm
  · exact (Bool.eq_false_iff.mpr h).symm

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) : QProgram n (PhysicalResult n k) :=
  (RefinedUpperRepairTrial.program hk chores active origin old q m L draw pi threshold eta lam tape).bind
    (fun result => .returned (finish hk chores active origin old L pi threshold eta lam result))

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) : PhysicalResult n k :=
  finish hk chores active origin old L pi threshold eta lam
    (RefinedUpperRepairTrial.execute policy hk chores active origin old q m L draw pi threshold eta lam tape)

theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L draw pi threshold eta lam tape)
      origin.history (execute policy hk chores active origin old q m L draw pi threshold eta lam tape) trace ∧
      (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.1.history = origin.history ++ trace ∧
      trace.length ≤ (k*q+m)*(n+1)+k*(r*(2*(n+1))) ∧
      (trace.map Prod.fst).countP isCut ≤ k*q+m+k*(r*2) := by
  obtain ⟨trace,he,hh,hq,hc⟩ := RefinedUpperRepairTrial.program_cost policy hk chores active origin old q m L draw pi threshold eta lam tape
  refine ⟨trace,?_,?_,hq,hc⟩
  · simpa only [program,execute,List.append_nil] using he.bind
      (fun result => Chores.QueryProgram.Program.returned (finish hk chores active origin old L pi threshold eta lam result))
      (Executes.returned _ _)
  · exact (finish_history hk chores active origin old L pi threshold eta lam _).trans hh

theorem program_cost_linear (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle)
    (hn : 1 ≤ n) (hcoarse : k*q ≤ m) (hretries : 2*k*r ≤ m) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L draw pi threshold eta lam tape)
      origin.history (execute policy hk chores active origin old q m L draw pi threshold eta lam tape) trace ∧
      (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6*n*m ∧ (trace.map Prod.fst).countP isCut ≤ 3*m := by
  obtain ⟨trace,he,hh,hq,hc⟩ := program_cost policy hk chores active origin old q m L draw pi threshold eta lam tape
  refine ⟨trace,he,hh,hq.trans ?_,hc.trans ?_⟩
  · calc
      _ = (k*q+m+2*k*r)*(n+1) := by ring
      _ ≤ (3*m)*(2*n) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  · nlinarith

variable {X : Type} [MeasurableSpace X]

theorem finish_measurable (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (L : ℕ)
    (pi : X → Equiv.Perm (Fin k)) (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (result : X → RefinedUpperRepairTrial.Result n k coarse fine)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hpi : Measurable pi) (ht : ∀ j, Measurable (fun x => threshold x j)) (hr : Measurable result) :
    Measurable (fun x => finish hk chores active (origin x) (old x) L (pi x) (threshold x) eta lam (result x)) := by
  have hd := measurable_fst.comp (measurable_fst.comp hr)
  have hcurrent := UpperCorrectionLoop.loop_current_measurable.comp (measurable_snd.comp hr)
  have hstage := RefinedUpperRepairAssembly.stage_measurable chores active eta lam result hr
  have ha := Measurable.of_eval (RefinedUpperRepairAllocation.allocation_measurable hk chores active origin old _
    L pi threshold _ ho hold hd hpi ht hstage)
  have hrem := RefinedUpperRepairRemaining.remaining_measurable hk active origin _ L pi threshold _ ho hd hpi ht hcurrent
  have hrestore : Measurable (fun x => (⟨(origin x).cells,(result x).2.current.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x => ((origin x).cells,(result x).2.current.history))
    exact (state_cells_measurable.comp ho).prodMk (state_history_measurable.comp hcurrent)
  exact ((Measurable.of_eval hold).prodMk (hrestore.prodMk measurable_const)).ite
    (measurableSet_eq_fun (UpperCorrectionLoop.loop_stopped_measurable.comp (measurable_snd.comp hr)) measurable_const)
    (ha.prodMk (hrem.prodMk measurable_const))

theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ)
    (draw : X → Fin m → Fin k × I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : X → Fin k → Fin r → UpperCircular.Circle)
    (ho : Measurable origin) (hold : ∀ j, Measurable (fun x => old x j))
    (hd : ∀ j, Measurable (fun x => draw x j)) (hpi : Measurable pi)
    (ht : ∀ j, Measurable (fun x => threshold x j)) (htape : ∀ j, Measurable (fun x => tape x j)) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L (draw x) (pi x) (threshold x) eta lam (tape x)) := by
  have hbase := RefinedUpperRepairTrial.program_certified hk chores active origin old q m L draw pi threshold eta lam tape ho hold hd hpi ht htape
  exact hbase.bind _ (Certified.returned _
    (finish_measurable hk chores active (fun z : X × RefinedUpperRepairTrial.Result n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m => origin z.1)
      (fun z => old z.1) L (fun z => pi z.1) (fun z => threshold z.1) eta lam Prod.snd
      (ho.comp measurable_fst) (fun j => (hold j).comp measurable_fst) (hpi.comp measurable_fst)
      (fun j => (ht j).comp measurable_fst) measurable_snd))

end EnvyFreeResearch.Full.RefinedUpperRepairProgram
