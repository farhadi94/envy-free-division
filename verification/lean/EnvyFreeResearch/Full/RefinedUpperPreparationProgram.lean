import EnvyFreeResearch.Full.RefinedUpperPreparationPackages
import EnvyFreeResearch.Full.RefinedUpperPreparationProbability
import EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable

/-! Policy-independent ordinary-query preparation with the actual determinant
selector, retained buffer, threshold packages and maximizing/minimizing
assignment. Every query remains in the output history, including when a later
stage rejects this preparation. Postprocessing issues no queries. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperPreparationProgram
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairJobs UpperQueryPrograms Chores.QueryProgram ProgramMeasurable RefinedUpperPreparation
variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

abbrev Prepared (n k coarse fine : ℕ) :=
  UpperGridData.Data n coarse fine × State n × (Fin k → State n) ×
    (Fin k → Fin k → ℝ) × Equiv.Perm (Fin k)

def finish (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (data : UpperGridData.Data n coarse fine) (L : ℕ)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) : Prepared n k coarse fine :=
  (data,dataRetained active origin data L,packages hk active origin old data L pi threshold,
    dataMatrix hk active origin old data L pi threshold,
    UpperRepairAllocation.assignment chores (dataMatrix hk active origin old data L pi threshold))

def program (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    QProgram n (Prepared n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m) :=
  (UpperRecordedGridProgram.prepare active origin q m draw).bind
    (fun data => .returned (finish hk chores active origin old data L pi threshold))

def execute (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    Prepared n k (UpperRecordedQuantiles.count (Agent := Fin k) q) m :=
  finish hk chores active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold

/-- Exact ordinary-program execution and trace, with no hidden queries in
selection, normalization, threshold allocation or assignment. -/
theorem program_cost (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    ∃ trace, Executes (totalPolicy policy) (program hk chores active origin old q m L draw pi threshold)
      origin.history (execute policy hk chores active origin old q m L draw pi threshold) trace ∧
      (execute policy hk chores active origin old q m L draw pi threshold).2.1.history = origin.history ++ trace ∧
      trace.length ≤ (k*q+m)*(n+1) ∧ (trace.map Prod.fst).countP isCut ≤ k*q+m := by
  obtain ⟨trace,he,hh⟩ := UpperRecordedGridProgram.prepare_executes policy active origin q m draw
  have hq := UpperGridMerge.query_bound policy active origin q m draw
  have hc := UpperGridMerge.cut_bound policy active origin q m draw
  rw [hh,List.length_append] at hq
  rw [hh,List.map_append,List.countP_append] at hc
  refine ⟨trace,?_,hh,?_,?_⟩
  · simpa only [program,List.append_nil] using he.bind
      (fun data => Chores.QueryProgram.Program.returned (finish hk chores active origin old data L pi threshold))
      (Executes.returned (execute policy hk chores active origin old q m L draw pi threshold) (origin.history ++ trace))
  · simpa only [Fintype.card_fin] using (Nat.le_of_add_le_add_left hq)
  · simp only [Fintype.card_fin] at hc
    omega

section Measurability
variable {X : Type} [MeasurableSpace X]

theorem finish_measurable (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : X → Equiv.Perm (Fin k)) (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (ho : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c)) (hd : Measurable data)
    (hpi : Measurable pi) (ht : ∀ j, Measurable (fun x => threshold x j)) :
    Measurable (fun x => finish hk chores active (origin x) (old x) (data x) L (pi x) (threshold x)) := by
  have hV := dataMatrix_measurable hk active origin old data L pi threshold ho hold hd hpi ht
  exact hd.prodMk ((dataRetained_measurable active origin data L ho hd).prodMk
    ((Measurable.of_eval (packages_measurable hk active origin old data L pi threshold ho hold hd hpi ht)).prodMk
      ((Measurable.of_eval (fun i => Measurable.of_eval (hV i))).prodMk
        (UpperRepairAllocation.assignment_measurable chores _ hV))))

/-- The compiled protocol has Borel next actions jointly in all old history,
coarse/fine random seeds, permutations and thresholds. -/
theorem program_certified (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (q m L : ℕ)
    (draw : X → Fin m → Fin k × I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k-1+1) → Fin (L+1))
    (ho : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c))
    (hdraw : ∀ a, Measurable (fun x => draw x a))
    (hpi : Measurable pi) (ht : ∀ j, Measurable (fun x => threshold x j)) :
    Certified (fun x => program hk chores active (origin x) (old x) q m L (draw x) (pi x) (threshold x)) := by
  have hbase := UpperRecordedGridProgramMeasurable.prepare_certified active origin q m draw ho hdraw
  exact hbase.bind _ (Certified.returned _
    (finish_measurable hk chores active (fun z : X × UpperGridData.Data n (UpperRecordedQuantiles.count (Agent := Fin k) q) m => origin z.1)
      (fun z => old z.1) Prod.snd L (fun z => pi z.1) (fun z => threshold z.1)
      (ho.comp measurable_fst) (fun c => (hold c).comp measurable_fst) measurable_snd
      (hpi.comp measurable_fst) (fun j => (ht j).comp measurable_fst)))

end Measurability
end EnvyFreeResearch.Full.RefinedUpperPreparationProgram
