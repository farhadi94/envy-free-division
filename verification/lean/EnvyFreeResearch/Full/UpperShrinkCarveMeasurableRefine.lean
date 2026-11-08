import EnvyFreeResearch.Full.UpperShrinkCarveMeasurable

/-! Borel certification of the actual variable-length refinement pass.
Fuel is the observable list length, so no discrete encoding of pieces is used. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  UpperQueryPrograms ProgramMeasurable ProtocolMeasurable Chores.QueryProgram
variable {n k : ℕ}

def refineFuel (active : Fin k → Fin n) : ℕ → List (Piece k) → History n → QProgram n (Mesh n k)
  | 0, _, history => .returned ⟨[],history⟩
  | fuel+1, pieces, history =>
    match pieces[0]? with
    | none => .returned ⟨[],history⟩
    | some piece =>
      if split piece then
        (medianChain (List.ofFn active) ⟨piece.cells,history⟩).bind (fun out =>
          (refineFuel active fuel pieces.tail out.history).bind (fun tail =>
            .returned ⟨children piece out ++ tail.pieces,tail.history⟩))
      else (refineFuel active fuel pieces.tail history).bind (fun tail =>
        .returned ⟨piece::tail.pieces,tail.history⟩)

theorem refineFuel_eq (active : Fin k → Fin n) (fuel : ℕ) (pieces : List (Piece k))
    (history : History n) (h : pieces.length ≤ fuel) :
    refineFuel active fuel pieces history = refinePieces active pieces history := by
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
      simp only [refineFuel,refinePieces,List.getElem?_cons_zero,List.tail_cons]
      simp_rw [ih rest _ hr]

theorem refineFuel_certified (active : Fin k → Fin n) (fuel : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] (pieces : X → List (Piece k)) (history : X → History n),
      Measurable pieces → Measurable history →
      Certified (fun x => refineFuel active fuel (pieces x) (history x)) := by
  induction fuel with
  | zero =>
    intro X _ pieces history hp hh
    exact Certified.returned _ (mesh_mk_measurable _ _ measurable_const hh)
  | succ fuel ih =>
    intro X _ pieces history hp hh
    have hhead := (measurable_list_getElem 0).comp hp
    have hfirst : Certified (fun z : X × Piece k =>
        medianChain (List.ofFn active) (⟨z.2.cells,history z.1⟩ : State n)) := by
      apply medianChain_certified
      exact measurable_comap_iff.mpr
        ((piece_cells_measurable.comp measurable_snd).prodMk (hh.comp measurable_fst))
    have htailYes : Certified (fun z : (X × Piece k) × State n =>
        refineFuel active fuel (pieces z.1.1).tail z.2.history) :=
      ih _ _ (measurable_list_tail.comp (hp.comp (measurable_fst.comp measurable_fst)))
        (state_history_measurable.comp measurable_snd)
    have hreturnYes : Measurable (fun z : ((X × Piece k) × State n) × Mesh n k =>
        (⟨children z.1.1.2 z.1.2 ++ z.2.pieces,z.2.history⟩ : Mesh n k)) := by
      apply mesh_mk_measurable
      · exact measurable_list_append.comp ((children_measurable _ _
          (measurable_snd.comp (measurable_fst.comp measurable_fst))
          (measurable_snd.comp measurable_fst)).prodMk (mesh_pieces_measurable.comp measurable_snd))
      · exact mesh_history_measurable.comp measurable_snd
    have hyes := hfirst.bind _ (htailYes.bind _ (Certified.returned _ hreturnYes))
    have htailNo : Certified (fun z : X × Piece k =>
        refineFuel active fuel (pieces z.1).tail (history z.1)) :=
      ih _ _ (measurable_list_tail.comp (hp.comp measurable_fst)) (hh.comp measurable_fst)
    have hreturnNo : Measurable (fun z : (X × Piece k) × Mesh n k =>
        (⟨z.1.2::z.2.pieces,z.2.history⟩ : Mesh n k)) := by
      apply mesh_mk_measurable
      · exact measurable_list_cons.comp ((measurable_snd.comp measurable_fst).prodMk
          (mesh_pieces_measurable.comp measurable_snd))
      · exact mesh_history_measurable.comp measurable_snd
    have hno := htailNo.bind _ (Certified.returned _ hreturnNo)
    have hbranch := Certified.branch (fun z : X × Piece k => decide (split z.2))
      (split_measurable.comp measurable_snd) _ _ hyes hno
    have habsent : Certified (fun x : X =>
        (Program.returned (⟨[],history x⟩ : Mesh n k) : QProgram n (Mesh n k))) :=
      Certified.returned (fun x : X => (⟨[],history x⟩ : Mesh n k))
        (mesh_mk_measurable _ _ measurable_const hh)
    apply (Certified.optionCases _ hhead _ _ hbranch habsent).congr
    intro x
    simp only [refineFuel,decide_eq_true_eq,Function.comp_def]
    cases (pieces x)[0]? <;> rfl

theorem refinePieces_certified {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (pieces : X → List (Piece k)) (history : X → History n)
    (hp : Measurable pieces) (hh : Measurable history) :
    Certified (fun x => refinePieces active (pieces x) (history x)) := by
  apply (Certified.natCases (fun x => (pieces x).length) (measurable_list_length.comp hp)
    (fun fuel x => refineFuel active fuel (pieces x) (history x))
    (fun fuel => refineFuel_certified active fuel pieces history hp hh)).congr
  intro x
  exact refineFuel_eq active _ _ _ le_rfl

end EnvyFreeResearch.Full.UpperShrinkCarve
