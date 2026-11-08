import EnvyFreeResearch.Full.ChoresOuterGroupProgram

/-! Sequential execution of all old-pool cohorts. Each query runs at the
actual accumulated history, while every cohort reads the same original
committed state. The results are collected before a pool commit. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

structure GroupResult where
  group : Cohort data hall cycle
  result : group.RunResult data hall cycle

def GroupResult.package (original : RootId → Snapshot.Output n) (out : GroupResult data hall cycle) :
    Package (Fin n) RootId := out.group.package data hall cycle original out.result

def GroupResult.Correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (original : RootId → Snapshot.Output n) (out : GroupResult data hall cycle) : Prop :=
  out.group.ResultCorrect data hall cycle cost original out.result

def batchProgram (original : RootId → Snapshot.Output n) :
    List (Cohort data hall cycle) → Program (Query (Fin n)) ℝ (Option (List (GroupResult data hall cycle)))
  | [] => .returned (some [])
  | group :: rest => (group.program data hall cycle original).bind (fun first =>
      match first with
      | none => .returned none
      | some result => (batchProgram original rest).bind (fun tail =>
          .returned (tail.map (fun outputs => ⟨group,result⟩ :: outputs))))

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)

include hsound hsep hr hH hscale good

theorem batch_executes (groups : List (Cohort data hall cycle))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ outputs : List (GroupResult data hall cycle), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (batchProgram data hall cycle (fun root => xs.get (index root)) groups)
        prior (some outputs) trace ∧
      outputs.map GroupResult.group=groups ∧
      (∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root))) ∧
      trace.length ≤ groups.length*ComponentRecording.budget n (Fintype.card (ComponentBatch.Task data.pending hall cycle)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤
        groups.length*SubCore.sourceBudget (Fintype.card (ComponentBatch.Task data.pending hall cycle)) := by
  induction groups generalizing prior with
  | nil => exact ⟨[],[],Executes.returned _ _,rfl,by simp,by simp,by simp⟩
  | cons group rest ih =>
    obtain ⟨first,t₁,hfirst,hcorrect₁,hQ₁,hC₁⟩ := cohort_executes data hall cycle cost xs index c
      hsound R H hsep hr hH hscale good group oracle hpolicy prior
    obtain ⟨tail,t₂,htail,hgroups,hcorrect₂,hQ₂,hC₂⟩ := ih (prior++t₁)
    let output : GroupResult data hall cycle := ⟨group,first⟩
    refine ⟨output::tail,t₁++t₂,?_,?_,?_,?_,?_⟩
    · have ht := htail.bind
        (fun tail => Program.returned (tail.map (fun outputs => output::outputs)))
        (Executes.returned _ ((prior++t₁)++t₂))
      have ht' : Executes oracle
          ((batchProgram data hall cycle (fun root => xs.get (index root)) rest).bind
            (fun tail => Program.returned (tail.map (fun outputs => output::outputs))))
          (prior++t₁) (some (output::tail)) t₂ := by
        simpa only [List.append_nil,Option.map_some] using ht
      exact hfirst.bind (fun first => match first with
        | none => Program.returned none
        | some result => (batchProgram data hall cycle (fun root => xs.get (index root)) rest).bind
            (fun tail => Program.returned (tail.map (fun outputs =>
              (⟨group,result⟩ : GroupResult data hall cycle)::outputs)))) ht'
    · simpa only [List.map_cons,hgroups,output]
    · intro out hout
      rcases List.mem_cons.mp hout with rfl | hout
      · exact hcorrect₁
      · exact hcorrect₂ out hout
    · simp only [List.length_append,List.length_cons,Nat.add_mul,one_mul]
      omega
    · simp only [List.countP_append,List.length_cons,Nat.add_mul,one_mul]
      omega

end EnvyFreeResearch.Full.Chores.Outer
