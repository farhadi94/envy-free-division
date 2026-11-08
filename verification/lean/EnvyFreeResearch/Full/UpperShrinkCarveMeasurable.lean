import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMeasurable
import EnvyFreeResearch.Full.UpperShrinkMedianMeasurable

/-! Borel certificates for the actual median-chain carve primitives. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  ProgramMeasurable ProtocolMeasurable Chores.QueryProgram
variable {n k : ℕ}

theorem piece_mk_measurable {X : Type} [MeasurableSpace X]
    (cells : X → List Component) (fraction : X → Option (Fin k) → ℝ)
    (hc : Measurable cells) (hf : Measurable fraction) :
    Measurable (fun x => (⟨cells x,fraction x⟩ : Piece k)) := by
  exact measurable_comap_iff.mpr (hc.prodMk hf)

theorem mesh_mk_measurable {X : Type} [MeasurableSpace X]
    (pieces : X → List (Piece k)) (history : X → History n)
    (hp : Measurable pieces) (hh : Measurable history) :
    Measurable (fun x => (⟨pieces x,history x⟩ : Mesh n k)) := by
  exact measurable_comap_iff.mpr (hp.prodMk hh)

theorem split_measurable : Measurable (fun p : Piece k => decide (split p)) := by
  apply decide_measurable
  simp only [split,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun c =>
    (measurableSet_lt measurable_const ((measurable_pi_apply c).comp piece_fraction_measurable)).inter
      (measurableSet_lt ((measurable_pi_apply c).comp piece_fraction_measurable) measurable_const))

theorem children_measurable {X : Type} [MeasurableSpace X]
    (piece : X → Piece k) (state : X → State n)
    (hp : Measurable piece) (hs : Measurable state) :
    Measurable (fun x => children (piece x) (state x)) := by
  apply list_map_measurable
  · exact piece_mk_measurable _ _ (measurable_list_singleton.comp measurable_snd)
      (piece_fraction_measurable.comp (hp.comp measurable_fst))
  · exact state_cells_measurable.comp hs

theorem medianChain_certified (cutters : List (Fin n)) :
    ∀ {X : Type} [MeasurableSpace X] (state : X → State n), Measurable state →
      Certified (fun x => medianChain cutters (state x)) := by
  induction cutters with
  | nil =>
    intro X _ state hs
    exact Certified.returned state hs
  | cons i rest ih =>
    intro X _ state hs
    have hfirst := UpperShrink.median_certified state (fun _ => i) hs measurable_const
    have htail := ih (fun z : X × (Option ℝ × State n) => z.2.2)
      (measurable_snd.comp measurable_snd)
    exact hfirst.bind _ htail

end EnvyFreeResearch.Full.UpperShrinkCarve
