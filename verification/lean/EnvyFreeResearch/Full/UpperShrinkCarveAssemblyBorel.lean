import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMesh

/-! Borel final assembly on variable-length meshes, with unchanged history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperComponentAssembly
  UpperDomainDifference ProtocolMeasurable
variable {n k : ℕ}

theorem mesh_selected_measurable (test : Piece k → Prop) [DecidablePred test]
    (ht : MeasurableSet {p | test p}) :
    Measurable (fun mesh : Mesh n k =>
      state ((mesh.pieces.filter test).flatMap Piece.cells) mesh.history) := by
  have htest : Measurable (fun p : Piece k => decide (test p)) := by
    apply decide_measurable
    exact ht
  have hkeep : Measurable (fun z : Mesh n k × Piece k => decide (test z.2)) :=
    htest.comp measurable_snd
  have hlist := list_filter_measurable (fun _ : Mesh n k => fun p => decide (test p))
    Mesh.pieces hkeep mesh_pieces_measurable
  exact state_measurable.comp
    ((list_flatMap_measurable (fun _ : Mesh n k => Piece.cells) _
      (piece_cells_measurable.comp measurable_snd) hlist).prodMk mesh_history_measurable)

theorem meshCarve_old_measurable (j : Fin k) :
    Measurable (fun mesh : Mesh n k => (meshCarve mesh).old j) := by
  apply mesh_selected_measurable
  exact measurableSet_eq_fun ((measurable_pi_apply (some j)).comp piece_fraction_measurable) measurable_const

theorem meshCarve_buffer_measurable :
    Measurable (fun mesh : Mesh n k => (meshCarve mesh).buffer) := by
  apply mesh_selected_measurable
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => (measurableSet_eq_fun
    ((measurable_pi_apply (some j)).comp piece_fraction_measurable) measurable_const).compl)

end EnvyFreeResearch.Full.UpperShrinkCarve
