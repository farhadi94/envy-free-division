import EnvyFreeResearch.Full.UpperGridRecords
import EnvyFreeResearch.Full.UpperQueryPrograms

/-! One actual median refinement, skipping a zero cached row. All original
observer endpoint records are charged, and the full domain is retained. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperQueryPrograms
  UpperUnionSampling UpperGridRecords Chores.QueryProgram UpperSamplingRecords

def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

def median (policy : Policy n) (state : State n) (cutter : Fin n) : Option ℝ × State n :=
  if total state cutter ≤ 0 then (none, state) else
    let result := sampleExecution policy state.history cutter (values state cutter)
      (total state cutter) state.cells half
    (some result.1, ⟨refineEndpoints state.cells [result.1], result.2⟩)

def medianProgram (state : State n) (cutter : Fin n) : QProgram n (Option ℝ × State n) :=
  if total state cutter ≤ 0 then .returned (none, state) else
    (sample state.history cutter (values state cutter) (total state cutter) state.cells half).bind
      (fun result => .returned (some result.1, ⟨refineEndpoints state.cells [result.1], result.2⟩))

theorem median_executes (policy : Policy n) (state : State n) (cutter : Fin n) :
    ∃ trace, Executes (totalPolicy policy) (medianProgram state cutter) state.history
      (median policy state cutter) trace ∧
      (median policy state cutter).2.history = state.history ++ trace := by
  by_cases hz : total state cutter ≤ 0
  · exact ⟨[], by simp only [medianProgram, median, hz, ite_true]; exact Executes.returned _ _,
      by simp [median, hz]⟩
  · obtain ⟨trace, hr, hh⟩ := sample_executes policy state.history cutter (values state cutter)
      (total state cutter) state.cells half
    refine ⟨trace, ?_, ?_⟩
    · have h := hr.bind (fun result => Program.returned
        (some result.1, (⟨refineEndpoints state.cells [result.1], result.2⟩ : State n)))
        (Executes.returned _ (state.history ++ trace))
      simpa only [medianProgram, median, hz, ite_false, List.append_nil] using h
    · simpa only [median, hz, ite_false] using hh

theorem median_domain (policy : Policy n) (state : State n) (cutter : Fin n) :
    domain (median policy state cutter).2.cells = domain state.cells := by
  unfold median
  split_ifs
  · rfl
  · exact refineEndpoints_domain _ _

theorem median_query_bound (policy : Policy n) (state : State n) (cutter : Fin n) :
    (median policy state cutter).2.history.length ≤ state.history.length + n + 1 := by
  unfold median
  split_ifs
  · dsimp only
    omega
  · exact sampleExecution_query_bound _ _ _ _ _ _ _

theorem median_cut_bound (policy : Policy n) (state : State n) (cutter : Fin n) :
    ((median policy state cutter).2.history.map Prod.fst).countP isCut ≤
      (state.history.map Prod.fst).countP isCut + 1 := by
  unfold median
  split_ifs
  · dsimp only
    omega
  · exact sampleExecution_cut_bound _ _ _ _ _ _ _

end EnvyFreeResearch.Full.UpperShrink
