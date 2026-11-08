import EnvyFreeResearch.Full.ProtocolMeasurable
import EnvyFreeResearch.Full.UpperProfiles

/-!
# Measurability of the concrete circular query stage

The two realized endpoint maps and the complete recorded history are proved
measurable from the ordinary joint measurability of a history-dependent policy.
Thus the stage's physical probability laws no longer require separate
measurability assumptions for its endpoints.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperStageMeasurable

open ProtocolMeasurable UpperCircularStage UpperCircular Chores

abbrev Circle := UpperCircular.Circle

variable {n : ℕ}

def MeasurablePolicy (policy : Policy n) : Prop :=
  Measurable (fun p : History n × Query n => policy p.1 p.2)

theorem executeQueries_ofFn_measurable {X : Type*} [MeasurableSpace X]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy) (m : ℕ)
    (queries : Fin m → X → Query n) (history : X → History n)
    (hqueries : ∀ i, Measurable (queries i)) (hhistory : Measurable history) :
    Measurable (fun x => executeQueries policy (List.ofFn (fun i => queries i x)) (history x)) := by
  induction m generalizing history with
  | zero => simpa only [List.ofFn_zero, executeQueries] using hhistory
  | succ m ih =>
    have hreply : Measurable (fun x => policy (history x) (queries 0 x)) :=
      hpolicy.comp (hhistory.prodMk (hqueries 0))
    have hupdated : Measurable
        (fun x => history x ++ [(queries 0 x, policy (history x) (queries 0 x))]) :=
      measurable_list_append.comp (hhistory.prodMk
        (measurable_list_singleton.comp ((hqueries 0).prodMk hreply)))
    simpa only [List.ofFn_succ, executeQueries] using
      ih (fun i => queries i.succ) _ (fun i => hqueries i.succ) hupdated

theorem firstQuery_measurable (cutter : Fin n) : Measurable (firstQuery cutter) :=
  measurable_query_cut.comp
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_subtype_coe.comp measurable_value))))

theorem lastQuery_measurable (cutter : Fin n) (amount : I) :
    Measurable (lastQuery cutter amount) :=
  measurable_query_cut.comp
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_subtype_coe.comp
        (measurable_value.comp (measurable_id.add_const (project amount)))))))

theorem firstEndpoint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) :
    Measurable (firstEndpoint policy history cutter) :=
  hpolicy.comp (measurable_const.prodMk (firstQuery_measurable cutter))

theorem afterFirst_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) :
    Measurable (afterFirst policy history cutter) := by
  apply executeQueries_ofFn_measurable
  · exact hpolicy
  · intro i
    exact measurable_query_eval.comp (measurable_const.prodMk
      (measurable_const.prodMk (firstEndpoint_measurable policy hpolicy history cutter)))
  · exact measurable_list_append.comp (measurable_const.prodMk
      (measurable_list_singleton.comp ((firstQuery_measurable cutter).prodMk
        (firstEndpoint_measurable policy hpolicy history cutter))))

theorem lastEndpoint_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (amount : I) :
    Measurable (lastEndpoint policy history cutter amount) :=
  hpolicy.comp ((afterFirst_measurable policy hpolicy history cutter).prodMk
    (lastQuery_measurable cutter amount))

theorem finalHistory_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (amount : I) :
    Measurable (finalHistory policy history cutter amount) := by
  apply executeQueries_ofFn_measurable
  · exact hpolicy
  · intro i
    exact measurable_query_eval.comp (measurable_const.prodMk
      (measurable_const.prodMk (lastEndpoint_measurable policy hpolicy history cutter amount)))
  · exact measurable_list_append.comp ((afterFirst_measurable policy hpolicy history cutter).prodMk
      (measurable_list_singleton.comp ((lastQuery_measurable cutter amount).prodMk
        (lastEndpoint_measurable policy hpolicy history cutter amount))))

/-- A jointly measurable complete optional-response policy supplies a jointly
measurable total real-response adapter. Legality is handled independently. -/
theorem answer_measurable (policy : AdaptiveOracle.Policy (Query n) ℝ)
    (hpolicy : Measurable (fun p : History n × Query n => policy p.1 p.2)) :
    MeasurablePolicy (AdaptiveOracle.answer policy) := by
  unfold MeasurablePolicy
  have h := measurable_option_cases (present := fun _ (reply : ℝ) => reply)
    (absent := fun _ => (0 : ℝ)) hpolicy measurable_snd measurable_const
  convert h using 1
  funext p
  unfold AdaptiveOracle.answer
  cases policy p.1 p.2 <;> rfl

theorem answer_admissible (P : IntervalOracle.Profile (Fin n))
    (policy : AdaptiveOracle.Policy (Query n) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P policy) :
    Admissible P (AdaptiveOracle.answer policy) :=
  fun history query hquery => (AdaptiveOracle.answer_spec P policy hpolicy history query hquery).2

/-- The implemented circular primitive under the full measurable legal-policy
contract, without assuming endpoint laws or endpoint measurability. -/
theorem measurable_circular_primitive (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cutter : Fin n) [IsProbabilityMeasure (μ cutter)]
    (hsupport : ∀ᵐ x ∂μ cutter, x ∈ Icc (0 : ℝ) 1)
    (policy : AdaptiveOracle.Policy (Query n) ℝ)
    (hlegal : AdaptiveOracle.IsLegalPolicy (measureProfile μ) policy)
    (hmeas : Measurable (fun p : History n × Query n => policy p.1 p.2))
    (history : History n) (amount : I) (foreign : Measure ℝ) [SFinite foreign] :
    (∀ start, (μ cutter).real
      (output (AdaptiveOracle.answer policy) history cutter amount start) = (amount : ℝ)) ∧
    (∀ start, (finalHistory (AdaptiveOracle.answer policy) history cutter amount start).length =
      history.length + 2 * (n + 1)) ∧
    (∀ start, ((finalHistory (AdaptiveOracle.answer policy) history cutter amount start).map
      Prod.fst).countP isCut = (history.map Prod.fst).countP isCut + 2) ∧
    ((∫⁻ start, foreign (output (AdaptiveOracle.answer policy) history cutter amount start)
      ∂(volume : Measure Circle)) = ENNReal.ofReal (amount : ℝ) * foreign (Icc 0 1)) :=
  UpperProfiles.circular_stage_primitive μ cutter hsupport (AdaptiveOracle.answer policy)
    (answer_admissible _ policy hlegal) history amount
    (firstEndpoint_measurable _ (answer_measurable policy hmeas) history cutter)
    (lastEndpoint_measurable _ (answer_measurable policy hmeas) history cutter amount) foreign

end EnvyFreeResearch.Full.UpperStageMeasurable
