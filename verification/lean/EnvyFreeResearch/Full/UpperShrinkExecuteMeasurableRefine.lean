import EnvyFreeResearch.Full.UpperShrinkExecuteMeasurableMedian

/-! Actual variable-length refinement output, retaining the complete history
from every preceding median call. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  ProtocolMeasurable ProgramMeasurable UpperStageMeasurable
variable {n k : ℕ}

def refineExecuteFuel (policy : Policy n) (active : Fin k → Fin n) :
    ℕ → List (Piece k) → History n → Mesh n k
  | 0, _, history => ⟨[],history⟩
  | fuel+1,pieces,history => match pieces[0]? with
    | none => ⟨[],history⟩
    | some piece =>
      if split piece then
        let out := medianChainExecute policy (List.ofFn active) ⟨piece.cells,history⟩
        let tail := refineExecuteFuel policy active fuel pieces.tail out.history
        ⟨children piece out ++ tail.pieces,tail.history⟩
      else
        let tail := refineExecuteFuel policy active fuel pieces.tail history
        ⟨piece::tail.pieces,tail.history⟩

theorem refineExecuteFuel_eq (policy : Policy n) (active : Fin k → Fin n)
    (fuel : ℕ) (pieces : List (Piece k)) (history : History n) (h : pieces.length ≤ fuel) :
    refineExecuteFuel policy active fuel pieces history = refinePiecesExecute policy active pieces history := by
  induction fuel generalizing pieces history with
  | zero =>
    have hp : pieces=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst pieces
    rfl
  | succ fuel ih =>
    cases pieces with
    | nil => rfl
    | cons piece rest =>
      have hr : rest.length ≤ fuel := by simpa only [List.length_cons,Nat.add_le_add_iff_right] using h
      simp only [refineExecuteFuel,refinePiecesExecute,List.getElem?_cons_zero,List.tail_cons]
      simp_rw [ih rest _ hr]

theorem refineExecuteFuel_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (fuel : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] (pieces : X → List (Piece k)) (history : X → History n),
      Measurable pieces → Measurable history →
      Measurable (fun x => refineExecuteFuel policy active fuel (pieces x) (history x)) := by
  induction fuel with
  | zero =>
    intro X _ pieces history hp hh
    exact mesh_mk_measurable _ _ measurable_const hh
  | succ fuel ih =>
    intro X _ pieces history hp hh
    have hfirst : Measurable (fun z : X × Piece k =>
        medianChainExecute policy (List.ofFn active) (⟨z.2.cells,history z.1⟩ : State n)) := by
      apply medianChainExecute_measurable policy hmeas
      exact measurable_comap_iff.mpr
        ((piece_cells_measurable.comp measurable_snd).prodMk (hh.comp measurable_fst))
    have htailYes := ih (fun z : X × Piece k => (pieces z.1).tail)
      (fun z => (medianChainExecute policy (List.ofFn active) ⟨z.2.cells,history z.1⟩).history)
      (measurable_list_tail.comp (hp.comp measurable_fst)) (state_history_measurable.comp hfirst)
    have hyes := mesh_mk_measurable _ _
      (measurable_list_append.comp ((children_measurable _ _ measurable_snd hfirst).prodMk
        (mesh_pieces_measurable.comp htailYes))) (mesh_history_measurable.comp htailYes)
    have htailNo := ih (fun z : X × Piece k => (pieces z.1).tail) (fun z => history z.1)
      (measurable_list_tail.comp (hp.comp measurable_fst)) (hh.comp measurable_fst)
    have hno := mesh_mk_measurable _ _
      (measurable_list_cons.comp (measurable_snd.prodMk (mesh_pieces_measurable.comp htailNo)))
      (mesh_history_measurable.comp htailNo)
    have hsplit : MeasurableSet {z : X × Piece k | split z.2} := by
      simpa only [Function.comp_def,decide_eq_true_eq] using
        measurableSet_eq_fun (split_measurable.comp measurable_snd) (measurable_const (a := true))
    let present (x : X) (piece : Piece k) : Mesh n k :=
      if split piece then
        let out := medianChainExecute policy (List.ofFn active) ⟨piece.cells,history x⟩
        let tail := refineExecuteFuel policy active fuel (pieces x).tail out.history
        ⟨children piece out ++ tail.pieces,tail.history⟩
      else
        let tail := refineExecuteFuel policy active fuel (pieces x).tail (history x)
        ⟨piece::tail.pieces,tail.history⟩
    have hpresent : Measurable (fun z : X × Piece k => present z.1 z.2) := hyes.ite hsplit hno
    have h := measurable_option_cases (present := present)
      (absent := fun x => (⟨[],history x⟩ : Mesh n k))
      ((measurable_list_getElem 0).comp hp) hpresent (mesh_mk_measurable _ _ measurable_const hh)
    convert h using 1
    funext x
    simp only [refineExecuteFuel,Function.comp_def]
    cases (pieces x)[0]? <;> rfl

theorem refinePiecesExecute_measurable {X : Type} [MeasurableSpace X]
    (policy : Policy n) (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n)
    (pieces : X → List (Piece k)) (history : X → History n)
    (hp : Measurable pieces) (hh : Measurable history) :
    Measurable (fun x => refinePiecesExecute policy active (pieces x) (history x)) := by
  have hall : Measurable (fun z : X × ℕ => refineExecuteFuel policy active z.2 (pieces z.1) (history z.1)) :=
    measurable_from_prod_countable_left (fun fuel => refineExecuteFuel_measurable policy hmeas active fuel pieces history hp hh)
  have h := hall.comp (measurable_id.prodMk (measurable_list_length.comp hp))
  convert h using 1
  funext x
  exact (refineExecuteFuel_eq policy active _ _ _ le_rfl).symm

end EnvyFreeResearch.Full.UpperShrinkCarve
