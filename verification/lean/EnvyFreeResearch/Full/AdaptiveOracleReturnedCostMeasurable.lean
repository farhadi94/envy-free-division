import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostSup
import EnvyFreeResearch.Full.UpperDomainDifferenceLists
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Measurability of actual single-protocol answered-cost suprema. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol ProtocolMeasurable
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}
  [MeasurableSpace Tape] [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output]

theorem history_marked_measurable (mark : Query → Bool) (hmark : Measurable mark) :
    Measurable (fun h : History Query Reply => (h.map Prod.fst).countP mark) := by
  have hm : Measurable (fun h : History Query Reply => h.map Prod.fst) :=
    UpperDomainDifference.list_map_measurable (fun _ e => e.1) (fun h : History Query Reply => h)
      (measurable_fst.comp measurable_snd) measurable_id
  have hf := UpperDomainDifference.list_filter_measurable (fun (_ : History Query Reply) q => mark q)
    (fun h => h.map Prod.fst) (hmark.comp measurable_snd) hm
  simpa only [List.countP_eq_length_filter,Function.comp_def] using measurable_list_length.comp hf

theorem queryCost_measurable (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : History Query Reply × Query => oracle p.1 p.2)) :
    Measurable (fun p : Tape × History Query Reply => queryCost next oracle p.1 p.2) := by
  apply Measurable.iSup
  intro fuel
  exact (Measurable.of_discrete (f := fun n : ℕ => (n:ℝ≥0∞))).comp
    (measurable_list_length.comp (measurable_execution_answered.comp
      (measurable_adaptive_run next oracle hnext horacle fuel)))

theorem markedCost_measurable (mark : Query → Bool) (hmark : Measurable mark)
    (next : Protocol Tape Query Reply Output) (oracle : Policy Query Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : History Query Reply × Query => oracle p.1 p.2)) :
    Measurable (fun p : Tape × History Query Reply => markedCost mark next oracle p.1 p.2) := by
  apply Measurable.iSup
  intro fuel
  exact (Measurable.of_discrete (f := fun n : ℕ => (n:ℝ≥0∞))).comp
    ((history_marked_measurable mark hmark).comp (measurable_execution_answered.comp
      (measurable_adaptive_run next oracle hnext horacle fuel)))

end EnvyFreeResearch.Full.AdaptiveOracle
