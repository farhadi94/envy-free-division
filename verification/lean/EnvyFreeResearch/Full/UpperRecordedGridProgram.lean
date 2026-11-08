import EnvyFreeResearch.Full.UpperProgramIteration
import EnvyFreeResearch.Full.UpperRecordedParents
import EnvyFreeResearch.Full.UpperInitialState

/-!
# Ordinary-query program for initialization and the complete common grid

All program definitions are input independent and contain no policy calls.
Operational equivalence connects them to the established physical, cache,
iid-law and measurable-output theorems for recorded grid construction.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRecordedGridProgram

open UpperCircularStage UpperRecordedDomain UpperCorrectionExecution UpperDomainDifference
  UpperGridRecords UpperQueryPrograms UpperProgramIteration Chores.QueryProgram

variable {n : ℕ} {Agent : Type*}

def grid (active : Agent → Fin n) (origin : State n) (m : ℕ) (draw : Fin m → Agent × I) :
    QProgram n ((Fin m → ℝ) × State n) :=
  (runProgram (fun history d => sample history (active d.1) (values origin (active d.1))
      (total origin (active d.1)) origin.cells d.2) m origin.history draw).bind (fun result =>
    .returned (result.1, ⟨refineEndpoints origin.cells (List.ofFn result.1), result.2⟩))

def quantiles [Fintype Agent] (active : Agent → Fin n) (origin : State n) (q : ℕ) :
    QProgram n ((Fin (UpperRecordedQuantiles.count (Agent := Agent) q) → ℝ) × State n) :=
  grid active origin _ (UpperQuantileExecution.schedule q)

def prepare [Fintype Agent] (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) :
    QProgram n ((Fin (UpperRecordedQuantiles.count (Agent := Agent) q) → ℝ) × (Fin m → ℝ) × State n) :=
  (quantiles active origin q).bind (fun coarse =>
    (grid active coarse.2 m draw).bind (fun result => .returned (coarse.1, result)))

def boot : QProgram n (State n) :=
  (queries [] (UpperInitialState.queries n)).bind (fun history =>
    .returned ⟨[UpperInitialState.unitComponent], history⟩)

def fromUnit [Fintype Agent] (active : Agent → Fin n) (q m : ℕ) (draw : Fin m → Agent × I) :
    QProgram n ((Fin (UpperRecordedQuantiles.count (Agent := Agent) q) → ℝ) × (Fin m → ℝ) × State n) :=
  boot.bind (fun origin => prepare active origin q m draw)

theorem grid_executes (policy : Policy n) (active : Agent → Fin n) (origin : State n)
    (m : ℕ) (draw : Fin m → Agent × I) :
    ∃ trace, Executes (totalPolicy policy) (grid active origin m draw) origin.history
      (UpperRecordedGrid.execute policy active origin m draw) trace ∧
      (UpperRecordedGrid.execute policy active origin m draw).2.history = origin.history ++ trace := by
  obtain ⟨trace, hrun, heq⟩ := runProgram_executes policy (fun h : History n => h)
    (fun history d => sample history (active d.1) (values origin (active d.1))
      (total origin (active d.1)) origin.cells d.2)
    (UpperRecordedGrid.step policy active origin)
    (fun h d => sample_executes policy h (active d.1) (values origin (active d.1))
      (total origin (active d.1)) origin.cells d.2) m origin.history draw
  refine ⟨trace, ?_, heq⟩
  have h := hrun.bind (fun result => Program.returned
      (result.1, (⟨refineEndpoints origin.cells (List.ofFn result.1), result.2⟩ : State n)))
    (Executes.returned (UpperRecordedGrid.execute policy active origin m draw) (origin.history ++ trace))
  simpa only [grid, List.append_nil] using h

theorem quantiles_executes [Fintype Agent] (policy : Policy n) (active : Agent → Fin n)
    (origin : State n) (q : ℕ) :
    ∃ trace, Executes (totalPolicy policy) (quantiles active origin q) origin.history
      (UpperRecordedQuantiles.run policy active origin q) trace ∧
      (UpperRecordedQuantiles.run policy active origin q).2.history = origin.history ++ trace :=
  grid_executes policy active origin _ _

theorem prepare_executes [Fintype Agent] (policy : Policy n) (active : Agent → Fin n)
    (origin : State n) (q m : ℕ) (draw : Fin m → Agent × I) :
    ∃ trace, Executes (totalPolicy policy) (prepare active origin q m draw) origin.history
      (UpperGridMerge.prepare policy active origin q m draw) trace ∧
      (UpperGridMerge.prepare policy active origin q m draw).2.2.history = origin.history ++ trace := by
  obtain ⟨firstTrace, hfirst, hfirstEq⟩ := quantiles_executes policy active origin q
  obtain ⟨lastTrace, hlast, hlastEq⟩ := grid_executes policy active
    (UpperRecordedQuantiles.run policy active origin q).2 m draw
  have htail := hlast.bind (fun result => Program.returned
      ((UpperRecordedQuantiles.run policy active origin q).1, result))
    (Executes.returned (UpperGridMerge.prepare policy active origin q m draw)
      ((UpperRecordedQuantiles.run policy active origin q).2.history ++ lastTrace))
  have htail' : Executes (totalPolicy policy)
      ((grid active (UpperRecordedQuantiles.run policy active origin q).2 m draw).bind
        (fun result => .returned ((UpperRecordedQuantiles.run policy active origin q).1, result)))
      (origin.history ++ firstTrace) (UpperGridMerge.prepare policy active origin q m draw) lastTrace := by
    rw [← hfirstEq]
    simpa only [List.append_nil] using htail
  refine ⟨firstTrace ++ lastTrace, hfirst.bind _ htail', ?_⟩
  change (UpperRecordedGrid.execute policy active (UpperRecordedQuantiles.run policy active origin q).2 m draw).2.history = _
  rw [hlastEq, hfirstEq, List.append_assoc]

theorem boot_executes (policy : Policy n) :
    ∃ trace, Executes (totalPolicy policy) (boot (n := n)) [] (UpperInitialState.boot policy) trace ∧
      (UpperInitialState.boot policy).history = trace := by
  obtain ⟨trace, hrun, heq⟩ := queries_executes policy [] (UpperInitialState.queries n)
  refine ⟨trace, ?_, ?_⟩
  · have h := hrun.bind (fun history => Program.returned
        (⟨[UpperInitialState.unitComponent], history⟩ : State n))
      (Executes.returned (UpperInitialState.boot policy) ([] ++ trace))
    simpa only [boot, List.append_nil] using h
  · simpa only [UpperInitialState.boot, List.nil_append] using heq

/-- The complete unit-resource grid is an actual compiled adaptive protocol,
with all initialization, quantile and sampling queries in its returned trace. -/
theorem fromUnit_protocol_run [Fintype Agent] (policy : Policy n) (active : Agent → Fin n)
    (q m : ℕ) (draw : Fin m → Agent × I) :
    ∃ trace, AdaptiveOracle.run (fromUnit active q m draw).protocol (totalPolicy policy) ()
        (2 * n + (Fintype.card Agent * q + m) * (n + 1)) [] =
      ⟨trace, .returned (UpperGridMerge.prepare policy active (UpperInitialState.boot policy) q m draw)⟩ ∧
      trace.length ≤ 2 * n + (Fintype.card Agent * q + m) * (n + 1) ∧
      (trace.map Prod.fst).countP isCut ≤ Fintype.card Agent * q + m := by
  obtain ⟨firstTrace, hfirst, hfirstEq⟩ := boot_executes policy
  obtain ⟨lastTrace, hlast, hlastEq⟩ := prepare_executes policy active (UpperInitialState.boot policy) q m draw
  have hlast' : Executes (totalPolicy policy)
      (prepare active (UpperInitialState.boot policy) q m draw) ([] ++ firstTrace)
      (UpperGridMerge.prepare policy active (UpperInitialState.boot policy) q m draw) lastTrace := by
    simpa only [List.nil_append, ← hfirstEq] using hlast
  have hrun := hfirst.bind (fun origin => prepare active origin q m draw) hlast'
  have heq : (UpperGridMerge.prepare policy active (UpperInitialState.boot policy) q m draw).2.2.history =
      firstTrace ++ lastTrace := by rw [hlastEq, hfirstEq]
  have hq := UpperGridMerge.query_bound policy active (UpperInitialState.boot policy) q m draw
  rw [heq, UpperInitialState.query_count] at hq
  have hc := UpperGridMerge.cut_bound policy active (UpperInitialState.boot policy) q m draw
  rw [heq, UpperInitialState.cut_count, zero_add] at hc
  exact ⟨firstTrace ++ lastTrace, hrun.run _ hq, hq, hc⟩

end EnvyFreeResearch.Full.UpperRecordedGridProgram
