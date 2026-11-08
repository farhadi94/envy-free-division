import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostAE
import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostReplay

/-! Answer-only Borel assumptions suffice for actual returned-protocol costs.
The measurable proxy totalizes undefined replies; exact returned-run replay
is proved without assuming that proxy is a legal oracle on all requests. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol ProtocolMeasurable
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}
  [MeasurableSpace Tape] [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output]

def totalizedPolicy (default : Reply) (oracle : Policy Query Reply) : Policy Query Reply :=
  fun history q => some ((oracle history q).getD default)

variable (next : Protocol Tape Query Reply Output) (oracle : Policy Query Reply)
  (default : Reply) (history : History Query Reply) (law : Measure Tape)
  (hreturn : ∀ᵐ tape ∂law, ∃ fuel trace out,
    run next oracle tape fuel history=⟨trace,.returned out⟩)

include hreturn in
theorem shared_return_totalized :
    ∀ᵐ tape ∂law, ∃ f g trace out,
      run next oracle tape f history=⟨trace,.returned out⟩ ∧
      run next (totalizedPolicy default oracle) tape g history=⟨trace,.returned out⟩ := by
  filter_upwards [hreturn] with tape ht
  obtain ⟨fuel,trace,out,h⟩ := ht
  exact ⟨fuel,fuel,trace,out,h,run_total_answer_of_returned next oracle default tape fuel history trace out h⟩

include hreturn in
theorem returned_costs_aemeasurable
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (hanswer : Measurable (fun p : History Query Reply × Query => (oracle p.1 p.2).getD default))
    (mark : Query → Bool) (hmark : Measurable mark) :
    AEMeasurable (fun tape => queryCost next oracle tape history) law ∧
    AEMeasurable (fun tape => markedCost mark next oracle tape history) law := by
  have hs := shared_return_totalized next oracle default history law hreturn
  have hm : Measurable (fun p : History Query Reply × Query => totalizedPolicy default oracle p.1 p.2) :=
    measurable_some.comp hanswer
  exact ⟨queryCost_aemeasurable_of_shared_return next oracle _ history law hs hnext hm,
    markedCost_aemeasurable_of_shared_return next oracle _ history law hs mark hmark hnext hm⟩

include hreturn in
theorem returned_costs_lintegral_totalized (mark : Query → Bool) :
    (∫⁻ tape, queryCost next oracle tape history ∂law)=
        (∫⁻ tape, queryCost next (totalizedPolicy default oracle) tape history ∂law) ∧
      (∫⁻ tape, markedCost mark next oracle tape history ∂law)=
        ∫⁻ tape, markedCost mark next (totalizedPolicy default oracle) tape history ∂law := by
  have hs := shared_return_totalized next oracle default history law hreturn
  exact ⟨returned_queryCost_lintegral_eq next oracle _ history law hs,
    returned_markedCost_lintegral_eq next oracle _ history law hs mark⟩

end EnvyFreeResearch.Full.AdaptiveOracle
