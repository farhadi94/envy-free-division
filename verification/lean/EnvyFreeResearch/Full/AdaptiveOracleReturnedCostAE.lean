import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostMeasurable

/-! Actual Option-oracle costs need not assume the entire policy is Borel.
Almost-everywhere legal replay to a Borel policy suffices for ordinary
expected query costs, with exact equality to the actual answered counts. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol ProtocolMeasurable
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}
  [MeasurableSpace Tape] [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output]

variable (next : Protocol Tape Query Reply Output) (oracle borelOracle : Policy Query Reply)
  (history : History Query Reply) (law : Measure Tape)
  (hreturn : ∀ᵐ tape ∂law, ∃ f g trace out,
    run next oracle tape f history=⟨trace,.returned out⟩ ∧
    run next borelOracle tape g history=⟨trace,.returned out⟩)

include hreturn in
theorem queryCost_ae_eq_of_shared_return :
    (fun tape => queryCost next oracle tape history) =ᵐ[law]
      (fun tape => queryCost next borelOracle tape history) := by
  filter_upwards [hreturn] with tape ht
  obtain ⟨f,g,trace,out,hf,hg⟩ := ht
  rw [returned_queryCost next oracle tape f history trace out hf,
    returned_queryCost next borelOracle tape g history trace out hg]

include hreturn in
theorem markedCost_ae_eq_of_shared_return (mark : Query → Bool) :
    (fun tape => markedCost mark next oracle tape history) =ᵐ[law]
      (fun tape => markedCost mark next borelOracle tape history) := by
  filter_upwards [hreturn] with tape ht
  obtain ⟨f,g,trace,out,hf,hg⟩ := ht
  rw [returned_markedCost mark next oracle tape f history trace out hf,
    returned_markedCost mark next borelOracle tape g history trace out hg]

include hreturn in
theorem queryCost_aemeasurable_of_shared_return
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : History Query Reply × Query => borelOracle p.1 p.2)) :
    AEMeasurable (fun tape => queryCost next oracle tape history) law := by
  have hm := (queryCost_measurable next borelOracle hnext horacle).comp
    (measurable_id.prodMk (measurable_const (a:=history)))
  exact hm.aemeasurable.congr (queryCost_ae_eq_of_shared_return next oracle borelOracle history law hreturn).symm

include hreturn in
theorem markedCost_aemeasurable_of_shared_return (mark : Query → Bool) (hmark : Measurable mark)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : History Query Reply × Query => borelOracle p.1 p.2)) :
    AEMeasurable (fun tape => markedCost mark next oracle tape history) law := by
  have hm := (markedCost_measurable mark hmark next borelOracle hnext horacle).comp
    (measurable_id.prodMk (measurable_const (a:=history)))
  exact hm.aemeasurable.congr (markedCost_ae_eq_of_shared_return next oracle borelOracle history law hreturn mark).symm

include hreturn in
theorem returned_queryCost_lintegral_eq :
    (∫⁻ tape, queryCost next oracle tape history ∂law)=
      ∫⁻ tape, queryCost next borelOracle tape history ∂law :=
  lintegral_congr_ae (queryCost_ae_eq_of_shared_return next oracle borelOracle history law hreturn)

include hreturn in
theorem returned_markedCost_lintegral_eq (mark : Query → Bool) :
    (∫⁻ tape, markedCost mark next oracle tape history ∂law)=
      ∫⁻ tape, markedCost mark next borelOracle tape history ∂law :=
  lintegral_congr_ae (markedCost_ae_eq_of_shared_return next oracle borelOracle history law hreturn mark)

end EnvyFreeResearch.Full.AdaptiveOracle
