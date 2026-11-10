import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.UpperRecordedGridProgramMeasurable
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolHistory
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMeasurable
import EnvyFreeResearch.Full.UpperQueryLegality

/-! Public unit-interval entry with paid records at both endpoints.
The actual trace has exactly 2n Eval calls and no Cuts. No initial cache
or implicit endpoint replies are supplied for free. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalUnit
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage RefinedUpperGlobalPhysical
  UpperQueryPrograms Chores.QueryProgram ProgramMeasurable
variable {n : ℕ}

def program : QProgram n (Anchor n) :=
  UpperRecordedGridProgram.boot.bind (fun origin => .returned (initial origin))

def execute (policy : Policy n) : Anchor n := initial (UpperInitialState.boot policy)

theorem initial_measurable : Measurable (initial (n := n)) := by
  apply anchor_mk_measurable
  · intro j
    exact UpperComponentAssembly.empty_measurable _ state_history_measurable
  · exact measurable_id
  · exact measurable_const

theorem program_certified : Certified (fun _ : Unit => (program : QProgram n (Anchor n))) := by
  exact UpperRecordedGridProgramMeasurable.boot_certified.bind _
    (Certified.returned _ (initial_measurable.comp measurable_snd))

theorem program_executes (policy : Policy n) :
    ∃ trace, Executes (totalPolicy policy) program [] (execute policy) trace ∧
      (execute policy).residue.history=trace ∧ trace.length=2*n ∧
      (trace.map Prod.fst).countP isCut=0 := by
  obtain ⟨trace,he,hh⟩ := UpperRecordedGridProgram.boot_executes policy
  refine ⟨trace,?_,hh,?_,?_⟩
  · simpa only [program,List.append_nil] using
      he.bind (fun origin => Program.returned (initial origin))
        (Executes.returned (execute policy) ([]++trace))
  · rw [← hh]
    exact UpperInitialState.query_count policy
  · rw [← hh]
    exact UpperInitialState.cut_count policy

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem entry_committed (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (direction : GlobalCompletion.Direction) :
    (execute policy).Committed μ direction (Icc 0 1) ∧ (execute policy).HistoryCompatible := by
  refine ⟨?_,initial_history _⟩
  simpa only [execute,UpperInitialState.initial_domain] using
    initial_committed μ direction (UpperInitialState.boot policy) (UpperInitialState.boot_wellFormed μ policy hp)

theorem entry_option_run (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (ho : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) :
    ∃ trace, AdaptiveOracle.run program.protocol oracle () (2*n) []=
      ⟨trace,.returned (execute (AdaptiveOracle.answer oracle))⟩ ∧
      trace.length=2*n ∧ (trace.map Prod.fst).countP isCut=0 ∧
      (execute (AdaptiveOracle.answer oracle)).residue.history=trace := by
  obtain ⟨trace,he,hh,hq,hc⟩ := program_executes (AdaptiveOracle.answer oracle)
  have hl : ∀ entry ∈ trace, IntervalOracle.Legal (Chores.measureProfile μ) entry.1 := by
    intro entry hm
    have hproj : trace.map Prod.fst=UpperInitialState.queries n := by
      rw [← hh]
      exact executeQueries_projection _ _ _
    apply UpperInitialState.queries_legal (Chores.measureProfile μ)
    rw [← hproj]
    exact List.mem_map.mpr ⟨entry,hm,rfl⟩
  have he' := UpperQueryLegality.option_replay (Chores.measureProfile μ) oracle ho he hl
  exact ⟨trace,he'.run (2*n) hq.le,hq,hc,hh⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalUnit
