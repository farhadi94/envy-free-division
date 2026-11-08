import EnvyFreeResearch.Full.UpperShrinkCarveMeasurable
import EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable

/-! Borel floating for the actual mesh with a data-dependent finite size.
Padded coordinates are used only in the measurability proof; at the actual
length they equal the real recorded pieces exactly. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  ProgramMeasurable ProtocolMeasurable
variable {n k : ℕ}

def paddedPiece (mesh : Mesh n k) (q : ℕ) : Piece k :=
  (mesh.pieces[q]?).getD ⟨[],fun _ => 0⟩

theorem paddedPiece_measurable (q : ℕ) : Measurable (fun mesh : Mesh n k => paddedPiece mesh q) :=
  UpperCorrectionOutputMeasurable.getD_measurable _
    ((measurable_list_getElem q).comp mesh_pieces_measurable) _

theorem paddedPiece_get (mesh : Mesh n k) (e : Fin mesh.pieces.length) :
    paddedPiece mesh e.val = mesh.pieces.get e := by
  simp [paddedPiece,List.getElem?_eq_getElem e.isLt,List.get_eq_getElem]

def floatedSized (active : Fin k → Fin n) (normal : Fin k → ℝ) (r : ℕ) (mesh : Mesh n k) : Mesh n k :=
  let a := fun i (e : Fin r) => total (⟨(paddedPiece mesh e.val).cells,mesh.history⟩ : State n) (active i) / normal i
  let plan := UpperFloating.select a
    (fun c : Fin r × Option (Fin k) => (paddedPiece mesh c.1.val).fraction c.2)
  ⟨List.ofFn (fun e : Fin r => ⟨(paddedPiece mesh e.val).cells,fun j => plan (e,j)⟩),mesh.history⟩

theorem floatedSized_eq (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k) :
    floatedSized active normal mesh.pieces.length mesh = floated active normal mesh := by
  unfold floatedSized floated
  simp only [paddedPiece_get]
  rfl

theorem floatedSized_measurable (active : Fin k → Fin n) (r : ℕ) :
    Measurable (fun z : (Fin k → ℝ) × Mesh n k => floatedSized active z.1 r z.2) := by
  have hp (e : Fin r) : Measurable (fun z : (Fin k → ℝ) × Mesh n k => paddedPiece z.2 e.val) :=
    (paddedPiece_measurable e.val).comp measurable_snd
  have hs (e : Fin r) : Measurable (fun z : (Fin k → ℝ) × Mesh n k =>
      (⟨(paddedPiece z.2 e.val).cells,z.2.history⟩ : State n)) :=
    measurable_comap_iff.mpr ((piece_cells_measurable.comp (hp e)).prodMk
      (mesh_history_measurable.comp measurable_snd))
  have ha (i : Fin k) (e : Fin r) : Measurable (fun z : (Fin k → ℝ) × Mesh n k =>
      total (⟨(paddedPiece z.2 e.val).cells,z.2.history⟩ : State n) (active i) / z.1 i) :=
    (total_measurable _ (fun _ => active i) (hs e) measurable_const).div
      ((measurable_pi_apply i).comp measurable_fst)
  have hi (c : Fin r × Option (Fin k)) : Measurable (fun z : (Fin k → ℝ) × Mesh n k =>
      (paddedPiece z.2 c.1.val).fraction c.2) :=
    (measurable_pi_apply c.2).comp (piece_fraction_measurable.comp (hp c.1))
  have hplan := UpperFloating.select_measurable _ _ ha hi
  apply mesh_mk_measurable
  · apply (UpperRecordedGrid.ofFn_measurable r).comp
    apply Measurable.of_eval
    intro e
    apply piece_mk_measurable
    · exact piece_cells_measurable.comp (hp e)
    · apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply (e,j)).comp hplan
  · exact mesh_history_measurable.comp measurable_snd

theorem floated_measurable (active : Fin k → Fin n) :
    Measurable (fun z : (Fin k → ℝ) × Mesh n k => floated active z.1 z.2) := by
  have hall : Measurable (fun z : ((Fin k → ℝ) × Mesh n k) × ℕ => floatedSized active z.1.1 z.2 z.1.2) :=
    measurable_from_prod_countable_left (floatedSized_measurable active)
  have h := hall.comp (measurable_id.prodMk
    (measurable_list_length.comp (mesh_pieces_measurable.comp measurable_snd)))
  convert h using 1
  funext z
  exact (floatedSized_eq active z.1 z.2).symm

end EnvyFreeResearch.Full.UpperShrinkCarve
