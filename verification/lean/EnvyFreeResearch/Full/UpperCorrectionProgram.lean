import EnvyFreeResearch.Full.UpperQueryPrograms

/-! Query-program compilation of the concrete two-endpoint correction. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperCorrectionProgram

open UpperCircularStage UpperRecordedDomain UpperUnionCircular UpperDomainDifference
  UpperCorrectionExecution UpperQueryPrograms Chores.QueryProgram

abbrev Circle := UpperCircular.Circle

def circular {n : ℕ} (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (total : ℝ) (cells : List Component) (amount : I) (start : Circle) : QProgram n (ℝ × ℝ × History n) :=
  (sample history cutter cache total cells (UpperCircular.value start)).bind (fun first =>
    (sample first.2 cutter cache total cells (UpperCircular.value (start + UpperCircular.project amount))).bind
      (fun last => .returned (first.1, last.1, last.2)))

def circularResult {n : ℕ} (policy : Policy n) (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) (start : Circle) :
    ℝ × ℝ × History n :=
  ((firstRun policy history cutter cache total cells start).1,
    (secondRun policy history cutter cache total cells amount start).1,
    (secondRun policy history cutter cache total cells amount start).2)

def correction {n : ℕ} (state : State n) (cutter : Fin n) (eps : ℝ) (start : Circle) :
    QProgram n (Correction × State n) :=
  (circular state.history cutter (values state cutter) (total state cutter) state.cells
    (amount eps (total state cutter)) start).bind (fun roots =>
      let record : Correction := ⟨amount eps (total state cutter), start, roots.1, roots.2.1⟩
      .returned (record, ⟨applyCorrection state.cells record, roots.2.2⟩))

variable {n : ℕ}

/-- The second program begins after the first Cut and every observer Eval.
Its complete trace is retained even for a subsequently rejected proposal. -/
theorem circular_executes (policy : Policy n) (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) (start : Circle) :
    ∃ trace, Executes (totalPolicy policy) (circular history cutter cache total cells amount start) history
      (circularResult policy history cutter cache total cells amount start) trace ∧
      (circularResult policy history cutter cache total cells amount start).2.2 = history ++ trace := by
  obtain ⟨firstTrace, hfirst, hfirstEq⟩ := sample_executes policy history cutter cache total cells (UpperCircular.value start)
  obtain ⟨lastTrace, hlast, hlastEq⟩ := sample_executes policy
    (firstRun policy history cutter cache total cells start).2 cutter cache total cells
    (UpperCircular.value (start + UpperCircular.project amount))
  have htail := hlast.bind (fun last => Program.returned
      ((firstRun policy history cutter cache total cells start).1, last.1, last.2))
    (Executes.returned (circularResult policy history cutter cache total cells amount start)
      ((firstRun policy history cutter cache total cells start).2 ++ lastTrace))
  have htail' : Executes (totalPolicy policy)
      ((sample (firstRun policy history cutter cache total cells start).2 cutter cache total cells
        (UpperCircular.value (start + UpperCircular.project amount))).bind
          (fun last => .returned ((firstRun policy history cutter cache total cells start).1, last.1, last.2)))
      (history ++ firstTrace) (circularResult policy history cutter cache total cells amount start) lastTrace := by
    rw [← hfirstEq]
    simpa only [firstRun, List.append_nil] using htail
  refine ⟨firstTrace ++ lastTrace, hfirst.bind _ htail', ?_⟩
  change (secondRun policy history cutter cache total cells amount start).2 = _
  change (secondRun policy history cutter cache total cells amount start).2 = _ at hlastEq
  rw [hlastEq]
  change (UpperUnionSampling.sampleExecution policy history cutter cache total cells
    (UpperCircular.value start)).2 ++ lastTrace = _
  rw [hfirstEq, List.append_assoc]

/-- Compiles the actual cache-reading, physical-removal transaction into
ordinary asks and pure returns, with no response-policy call in the program. -/
theorem correction_executes (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) :
    ∃ trace, Executes (totalPolicy policy) (correction state cutter eps start) state.history
      (UpperCorrectionExecution.execute policy state cutter eps start) trace ∧
      (UpperCorrectionExecution.execute policy state cutter eps start).2.history = state.history ++ trace := by
  obtain ⟨trace, hrun, heq⟩ := circular_executes policy state.history cutter (values state cutter)
    (total state cutter) state.cells (amount eps (total state cutter)) start
  refine ⟨trace, ?_, heq⟩
  have h := hrun.bind (fun roots =>
      let record : Correction := ⟨amount eps (total state cutter), start, roots.1, roots.2.1⟩
      Program.returned (record, (⟨applyCorrection state.cells record, roots.2.2⟩ : State n)))
    (Executes.returned (UpperCorrectionExecution.execute policy state cutter eps start) (state.history ++ trace))
  simpa only [correction, List.append_nil] using h

/-- All exploratory calls are present in the compiled trace; its deterministic
charge includes every zero/full/default branch. -/
theorem correction_executes_bounded (policy : Policy n) (state : State n) (cutter : Fin n)
    (eps : ℝ) (start : Circle) :
    ∃ trace, Executes (totalPolicy policy) (correction state cutter eps start) state.history
      (UpperCorrectionExecution.execute policy state cutter eps start) trace ∧
      (UpperCorrectionExecution.execute policy state cutter eps start).2.history = state.history ++ trace ∧
      trace.length ≤ 2 * (n + 1) ∧ (trace.map Prod.fst).countP isCut ≤ 2 := by
  obtain ⟨trace, hrun, heq⟩ := correction_executes policy state cutter eps start
  have hq := UpperCorrectionExecution.query_bound policy state cutter eps start
  have hc := UpperCorrectionExecution.cut_bound policy state cutter eps start
  rw [heq, List.length_append] at hq
  rw [heq, List.map_append, List.countP_append] at hc
  exact ⟨trace, hrun, heq, by omega, by omega⟩

end EnvyFreeResearch.Full.UpperCorrectionProgram
