import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeCore
import EnvyFreeResearch.Full.UpperZeroRowsMeasurable
import EnvyFreeResearch.Full.UpperBaseCasesMeasurable

/-! Borel cached preprocessing and terminal physical joins. The measurable
structure retains the real-valued endpoint and complete transcript data. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open MeasureTheory RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution
open UpperComponentAssembly UpperZeroRows
open scoped Classical
variable {n : ℕ} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem finite_select_measurable {I : Type} [MeasurableSpace I] [MeasurableSingletonClass I]
    [Countable I] (index : X → I) (hi : Measurable index) (f : I → X → Y)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => f (index x) x) := by
  have h : Measurable (fun p : X × I => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hi)

theorem terminal_measurable (a : X → Anchor n) (ha : Measurable a)
    (addition : X → Fin n → State n) (hadd : Measurable addition)
    (history : X → UpperCircularStage.History n) (hh : Measurable history) :
    Measurable (fun x => terminal (a x) (addition x) (history x)) := by
  apply anchor_mk_measurable
  · intro j
    exact join_measurable _ _ _ (anchor_bundle_measurable a ha j)
      ((measurable_pi_apply j).comp hadd) hh
  · exact empty_measurable _ hh
  · exact anchor_active_measurable.comp ha

theorem giveAllTerminal_fixed_measurable (recipient : Fin n) :
    Measurable (fun a : Anchor n => giveAllTerminal a recipient) :=
  terminal_measurable id measurable_id _
    (Measurable.of_eval (fun j => giveAll_measurable _ anchor_residue_measurable recipient j))
    _ (state_history_measurable.comp anchor_residue_measurable)

theorem giveAllTerminal_measurable (recipient : X → Fin n) (hr : Measurable recipient)
    (a : X → Anchor n) (ha : Measurable a) :
    Measurable (fun x => giveAllTerminal (a x) (recipient x)) :=
  finite_select_measurable recipient hr _ (fun i => (giveAllTerminal_fixed_measurable i).comp ha)

theorem anchor_zeroRows_measurable :
    Measurable (fun a : Anchor n => zeroRows a.residue a.active) :=
  finite_select_measurable _ anchor_active_measurable _
    (fun active => zeroRows_measurable _ anchor_residue_measurable active)

theorem anchor_positiveRows_measurable :
    Measurable (fun a : Anchor n => positiveRows a.residue a.active) :=
  finite_select_measurable _ anchor_active_measurable _
    (fun active => positiveRows_measurable _ anchor_residue_measurable active)

theorem freezeZero_measurable : Measurable (freezeZero (n := n)) := by
  apply anchor_mk_measurable
  · intro j
    exact anchor_bundle_measurable id measurable_id j
  · exact anchor_residue_measurable
  · exact anchor_positiveRows_measurable

theorem pick_measurable (fallback : Fin n) : Measurable (pick fallback) := measurable_of_countable _

theorem second_measurable (fallback : Fin n) : Measurable (second fallback) := measurable_of_countable _

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
