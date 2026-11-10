import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolPublicPolynomial
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurable
import EnvyFreeResearch.Full.UpperDomainDifferenceLists

/-! The actual all-attempt query/Cut totals are measurable extended-natural
random variables, so their lintegral bounds are ordinary expectations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperStageMeasurable ProtocolMeasurable
variable {n : ℕ}

theorem isCut_measurable : Measurable (isCut (n:=n)) :=
  measurable_query_cases measurable_const measurable_const

theorem historyCuts_measurable : Measurable (fun h : History n => (h.map Prod.fst).countP isCut) := by
  have hm : Measurable (fun h : History n => h.map Prod.fst) :=
    UpperDomainDifference.list_map_measurable (fun _ e => e.1) (fun h : History n => h)
      (measurable_fst.comp measurable_snd) measurable_id
  have hf := UpperDomainDifference.list_filter_measurable (fun (_ : History n) q => isCut q)
    (fun h => h.map Prod.fst) (isCut_measurable.comp measurable_snd) hm
  simpa only [List.countP_eq_length_filter,Function.comp_def] using measurable_list_length.comp hf

theorem runQueries_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) (t : ℕ) :
    Measurable (fun omega => runQueries policy fallback chores initial omega t) := by
  have hr := RefinedUpperGlobalRun.run_measurable (Phase.step policy fallback chores)
    (RefinedUpperGlobalRun.DispatchMeasurable.step_measurable policy hmeas fallback chores) initial t
  exact (Measurable.of_discrete (f:=fun m : ℕ => m-initial.history.length)).comp
    (measurable_list_length.comp (phase_history_measurable.comp hr))

theorem runCuts_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) (t : ℕ) :
    Measurable (fun omega => runCuts policy fallback chores initial omega t) := by
  have hr := RefinedUpperGlobalRun.run_measurable (Phase.step policy fallback chores)
    (RefinedUpperGlobalRun.DispatchMeasurable.step_measurable policy hmeas fallback chores) initial t
  exact (Measurable.of_discrete (f:=fun m : ℕ => m-(initial.history.map Prod.fst).countP isCut)).comp
    (historyCuts_measurable.comp (phase_history_measurable.comp hr))

theorem totalQueries_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) :
    Measurable (totalQueries policy fallback chores initial) := by
  apply Measurable.iSup
  intro t
  exact (Measurable.of_discrete (f:=fun m : ℕ => (m:ℝ≥0∞))).comp
    (runQueries_measurable policy hmeas fallback chores initial t)

theorem totalCuts_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) :
    Measurable (totalCuts policy fallback chores initial) := by
  apply Measurable.iSup
  intro t
  exact (Measurable.of_discrete (f:=fun m : ℕ => (m:ℝ≥0∞))).comp
    (runCuts_measurable policy hmeas fallback chores initial t)

theorem unitQueries_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) : Measurable (unitQueries policy fallback chores) :=
  measurable_const.add (totalQueries_measurable policy hmeas fallback chores (unitInitial policy))

theorem unitCuts_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) : Measurable (unitCuts policy fallback chores) :=
  totalCuts_measurable policy hmeas fallback chores (unitInitial policy)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
