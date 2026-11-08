import EnvyFreeResearch.Full.UpperShrinkCarveAssembly
import EnvyFreeResearch.Full.UpperShrinkCarveProgram

/-! The actual finite color grouping uses the ordinary Borel coding of
endpoint lists and real fraction tables, not a discrete coding of valuations. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperComponentAssembly
  ProtocolMeasurable
variable {n r k : ℕ}

def pieceCode (piece : Piece k) := (piece.cells,piece.fraction)
instance pieceMeasurableSpace : MeasurableSpace (Piece k) :=
  MeasurableSpace.comap pieceCode inferInstance
theorem pieceCode_measurable : Measurable (pieceCode (k := k)) := comap_measurable _
theorem piece_cells_measurable : Measurable (Piece.cells (k := k)) :=
  measurable_fst.comp pieceCode_measurable
theorem piece_fraction_measurable : Measurable (Piece.fraction (k := k)) :=
  measurable_snd.comp pieceCode_measurable

def meshCode (mesh : Mesh n k) := (mesh.pieces,mesh.history)
instance meshMeasurableSpace : MeasurableSpace (Mesh n k) :=
  MeasurableSpace.comap meshCode inferInstance
theorem meshCode_measurable : Measurable (meshCode (n := n) (k := k)) := comap_measurable _
theorem mesh_pieces_measurable : Measurable (Mesh.pieces (n := n) (k := k)) :=
  measurable_fst.comp meshCode_measurable
theorem mesh_history_measurable : Measurable (Mesh.history (n := n) (k := k)) :=
  measurable_snd.comp meshCode_measurable

variable {X : Type} [MeasurableSpace X]

theorem selectedState_measurable (pieces : X → Fin r → State n)
    (history : X → History n) (selected : X → Finset (Fin r))
    (hp : ∀ e, Measurable (fun z => pieces z e)) (hh : Measurable history)
    (hs : Measurable selected) :
    Measurable (fun z => selectedState (pieces z) (history z) (selected z)) := by
  apply family_measurable _ history _ hh
  intro e
  exact (hp e).ite ((measurableSet_mem_finset e).preimage hs) (empty_measurable history hh)

theorem dummyCells_measurable (x : X → Fin r → Option (Fin k) → ℝ)
    (hx : ∀ e c, Measurable (fun z => x z e c)) : Measurable (fun z => dummyCells (x z)) := by
  apply measurable_finset_iff.mpr
  intro e
  apply measurableSet_setOfPred.mp
  simp only [dummyCells,Finset.mem_filter,Finset.mem_univ,true_and,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => (measurableSet_eq_fun (hx e (some j)) measurable_const).compl)

theorem assembled_old_measurable (pieces : X → Fin r → State n)
    (history : X → History n) (x : X → Fin r → Option (Fin k) → ℝ)
    (hp : ∀ e, Measurable (fun z => pieces z e)) (hh : Measurable history)
    (hx : ∀ e c, Measurable (fun z => x z e c)) (j : Fin k) :
    Measurable (fun z => (assembledCarve (pieces z) (history z) (x z)).old j) :=
  selectedState_measurable pieces history _ hp hh
    (UpperWholePaymentsPhysical.integralCells_measurable x hx j)

theorem assembled_buffer_measurable (pieces : X → Fin r → State n)
    (history : X → History n) (x : X → Fin r → Option (Fin k) → ℝ)
    (hp : ∀ e, Measurable (fun z => pieces z e)) (hh : Measurable history)
    (hx : ∀ e c, Measurable (fun z => x z e c)) :
    Measurable (fun z => (assembledCarve (pieces z) (history z) (x z)).buffer) :=
  selectedState_measurable pieces history _ hp hh (dummyCells_measurable x hx)

end EnvyFreeResearch.Full.UpperShrinkCarve
