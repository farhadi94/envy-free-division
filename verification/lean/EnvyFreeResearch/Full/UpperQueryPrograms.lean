import EnvyFreeResearch.Full.ChoresProgram
import EnvyFreeResearch.Full.UpperCorrectionExecution

/-!
# Ordinary-query programs for the upper-bound leaf executors

Program definitions contain only ordinary asks, finite arithmetic and pure
returns. They do not call a response policy. Their operational proofs recover
the exact outputs and complete histories of the already verified executors.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperQueryPrograms

open UpperCircularStage UpperRecordedDomain UpperUnionSampling UpperUnionCircular
  UpperDomainDifference UpperCorrectionExecution
open Chores.QueryProgram

abbrev QProgram (n : ℕ) (Output : Type*) := Program (Query n) ℝ Output

def totalPolicy {n : ℕ} (policy : Policy n) : AdaptiveOracle.Policy (Query n) ℝ :=
  fun history query => some (policy history query)

def queries {n : ℕ} (history : History n) : List (Query n) → QProgram n (History n)
  | [] => .returned history
  | q :: rest => .ask q (fun reply => queries (history ++ [(q, reply)]) rest)

def route {n : ℕ} (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (target : ℝ) (r : Route Component) : QProgram n (ℝ × History n) :=
  let residual := target - sumValues cache r.before
  if residual = cache r.cell then .returned (r.cell.right, history) else
  let query := componentQuery cutter r.cell residual
  .ask query (fun endpoint =>
    (queries (history ++ [(query, endpoint)]) (recordings n endpoint)).bind
      (fun recorded => .returned (endpoint, recorded)))

def domainCut {n : ℕ} (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (target : ℝ) (cells : List Component) : QProgram n (Option (ℝ × History n)) :=
  match locate cache target cells with
  | none => .returned none
  | some r => (route history cutter cache target r).bind (fun result => .returned (some result))

def sample {n : ℕ} (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (total : ℝ) (cells : List Component) (draw : I) : QProgram n (ℝ × History n) :=
  (domainCut history cutter cache ((draw : ℝ) * total) cells).bind
    (fun result => .returned (result.getD (0, history)))

variable {n : ℕ}

/-- Complete actual trace of all the ordinary Eval recordings. -/
theorem queries_executes (policy : Policy n) (history : History n) (qs : List (Query n)) :
    ∃ trace, Executes (totalPolicy policy) (queries history qs) history
      (executeQueries policy qs history) trace ∧ executeQueries policy qs history = history ++ trace := by
  induction qs generalizing history with
  | nil => exact ⟨[], Executes.returned _ _, by simp [executeQueries]⟩
  | cons q qs ih =>
    obtain ⟨trace, hrun, heq⟩ := ih (history ++ [(q, policy history q)])
    refine ⟨(q, policy history q) :: trace, ?_, ?_⟩
    · exact Executes.ask q _ history (policy history q) _ trace rfl hrun
    · simpa only [executeQueries, List.append_assoc, List.singleton_append] using heq

/-- The cached-boundary branch performs no ask. The other branch performs
one Cut followed by every original observer's actual recording. -/
theorem route_executes (policy : Policy n) (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (target : ℝ) (r : Route Component) :
    ∃ trace, Executes (totalPolicy policy) (route history cutter cache target r) history
      (executeRoute policy history cutter cache target r) trace ∧
      (executeRoute policy history cutter cache target r).2 = history ++ trace := by
  by_cases hb : target - sumValues cache r.before = cache r.cell
  · simp only [route, executeRoute, hb, ite_true]
    exact ⟨[], Executes.returned _ _, by simp⟩
  · let query := componentQuery cutter r.cell (target - sumValues cache r.before)
    let endpoint := policy history query
    obtain ⟨trace, hrun, heq⟩ := queries_executes policy (history ++ [(query, endpoint)]) (recordings n endpoint)
    have hpair := hrun.bind (fun recorded => Program.returned (endpoint, recorded))
      (Executes.returned (endpoint, executeQueries policy (recordings n endpoint)
        (history ++ [(query, endpoint)])) ((history ++ [(query, endpoint)]) ++ trace))
    refine ⟨(query, endpoint) :: trace, ?_, ?_⟩
    · simp only [route, executeRoute, hb, ite_false]
      apply Executes.ask _ _ history endpoint _ trace rfl
      simpa only [List.append_nil] using hpair
    · simp only [executeRoute, hb, ite_false]
      simpa only [List.append_assoc, List.singleton_append] using heq

theorem domainCut_executes (policy : Policy n) (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (target : ℝ) (cells : List Component) :
    ∃ trace, Executes (totalPolicy policy) (domainCut history cutter cache target cells) history
      (executeDomain policy history cutter cache target cells) trace ∧
      match executeDomain policy history cutter cache target cells with
      | none => trace = []
      | some result => result.2 = history ++ trace := by
  cases hl : locate cache target cells with
  | none =>
    simp only [domainCut, executeDomain, hl, Option.map_none]
    exact ⟨[], Executes.returned _ _, rfl⟩
  | some r =>
    obtain ⟨trace, hrun, heq⟩ := route_executes policy history cutter cache target r
    refine ⟨trace, ?_, ?_⟩
    · simp only [domainCut, executeDomain, hl, Option.map_some]
      have h := hrun.bind (fun result => Program.returned (some result))
        (Executes.returned (some (executeRoute policy history cutter cache target r)) (history ++ trace))
      simpa only [List.append_nil] using h
    · simpa only [executeDomain, hl, Option.map_some] using heq

/-- The total sampler program exactly matches the existing executor on all
inputs, including its explicit default branch for malformed data. -/
theorem sample_executes (policy : Policy n) (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (total : ℝ) (cells : List Component) (draw : I) :
    ∃ trace, Executes (totalPolicy policy) (sample history cutter cache total cells draw) history
      (sampleExecution policy history cutter cache total cells draw) trace ∧
      (sampleExecution policy history cutter cache total cells draw).2 = history ++ trace := by
  obtain ⟨trace, hrun, heq⟩ := domainCut_executes policy history cutter cache ((draw : ℝ) * total) cells
  refine ⟨trace, ?_, ?_⟩
  · have h := hrun.bind (fun result => Program.returned (result.getD (0, history)))
      (Executes.returned (sampleExecution policy history cutter cache total cells draw) (history ++ trace))
    simpa only [sample, sampleExecution, List.append_nil] using h
  · cases hd : executeDomain policy history cutter cache ((draw : ℝ) * total) cells with
    | none =>
      have ht : trace = [] := by simpa only [hd] using heq
      simp only [sampleExecution, hd, Option.getD_none, ht, List.append_nil]
    | some result => simpa only [sampleExecution, hd, Option.getD_some] using heq

/-- Compiling the leaf program yields the exact actual adaptive next-action
run with the same result and complete charged trace. -/
theorem sample_protocol_run (policy : Policy n) (cutter : Fin n) (cache : Component → ℝ)
    (total : ℝ) (cells : List Component) (draw : I) :
    ∃ trace, AdaptiveOracle.run (sample [] cutter cache total cells draw).protocol
      (totalPolicy policy) () (n + 1) [] =
        ⟨trace, .returned (sampleExecution policy [] cutter cache total cells draw)⟩ ∧
      trace.length ≤ n + 1 := by
  obtain ⟨trace, hrun, heq⟩ := sample_executes policy [] cutter cache total cells draw
  have hb := sampleExecution_query_bound policy [] cutter cache total cells draw
  have ht : trace.length ≤ n + 1 := by
    simpa only [heq, List.nil_append, List.length_nil, zero_add] using hb
  exact ⟨trace, hrun.run (n + 1) ht, ht⟩

end EnvyFreeResearch.Full.UpperQueryPrograms
