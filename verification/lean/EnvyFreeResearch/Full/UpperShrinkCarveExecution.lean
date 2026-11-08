import EnvyFreeResearch.Full.UpperShrinkCarveProgram

/-! Operational execution and charging for one actual refinement pass.
Only split parents make median calls; already integral pieces pass through
unchanged. All median calls see the complete accumulated history. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperQueryPrograms
  Chores.QueryProgram

def splitCount (pieces : List (Piece k)) : ℕ := (pieces.filter (fun p => decide (split p))).length

def refinePiecesExecute (policy : Policy n) (active : Fin k → Fin n)
    (pieces : List (Piece k)) (history : History n) : Mesh n k :=
  match pieces with
  | [] => ⟨[],history⟩
  | piece :: rest =>
    if split piece then
      let out := medianChainExecute policy (List.ofFn active) ⟨piece.cells,history⟩
      let tail := refinePiecesExecute policy active rest out.history
      ⟨children piece out ++ tail.pieces,tail.history⟩
    else
      let tail := refinePiecesExecute policy active rest history
      ⟨piece :: tail.pieces,tail.history⟩

theorem refinePieces_executes (policy : Policy n) (active : Fin k → Fin n)
    (pieces : List (Piece k)) (history : History n) :
    ∃ trace, Executes (totalPolicy policy) (refinePieces active pieces history) history
      (refinePiecesExecute policy active pieces history) trace ∧
      (refinePiecesExecute policy active pieces history).history = history ++ trace := by
  induction pieces generalizing history with
  | nil => exact ⟨[],Executes.returned _ _,by simp [refinePiecesExecute]⟩
  | cons piece rest ih =>
    by_cases hs : split piece
    · let out := medianChainExecute policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)
      obtain ⟨first,hfirst,hh⟩ := medianChain_executes policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)
      obtain ⟨tail,htail,hhtail⟩ := ih out.history
      refine ⟨first++tail,?_,?_⟩
      · have hret := htail.bind (fun result => Program.returned
          (⟨children piece out ++ result.pieces,result.history⟩ : Mesh n k))
          (Executes.returned _ (out.history++tail))
        simp only [List.append_nil] at hret
        have h := hfirst.bind (fun result => (refinePieces active rest result.history).bind
          (fun result' => .returned (⟨children piece result ++ result'.pieces,result'.history⟩ : Mesh n k)))
          (by rw [← hh]; exact hret)
        simpa only [refinePieces,refinePiecesExecute,hs,ite_true] using h
      · simp only [refinePiecesExecute,hs,ite_true]
        change (refinePiecesExecute policy active rest out.history).history = _
        rw [hhtail]
        change out.history++tail = history++(first++tail)
        rw [hh,List.append_assoc]
    · obtain ⟨tail,htail,hh⟩ := ih history
      refine ⟨tail,?_,?_⟩
      · have h := htail.bind (fun result => Program.returned (⟨piece::result.pieces,result.history⟩ : Mesh n k))
          (Executes.returned _ (history++tail))
        simpa only [refinePieces,refinePiecesExecute,hs,ite_false,List.append_nil] using h
      · simpa only [refinePiecesExecute,hs,ite_false] using hh

theorem refinePieces_query_bound (policy : Policy n) (active : Fin k → Fin n)
    (pieces : List (Piece k)) (history : History n) :
    (refinePiecesExecute policy active pieces history).history.length ≤
      history.length + splitCount pieces*k*(n+1) := by
  induction pieces generalizing history with
  | nil => simp [refinePiecesExecute,splitCount]
  | cons piece rest ih =>
    by_cases hs : split piece
    · have hfirst := medianChain_query_bound policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)
      have htail := ih (medianChainExecute policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)).history
      simp only [List.length_ofFn] at hfirst
      simp only [refinePiecesExecute,hs,ite_true]
      have hcount : splitCount (piece::rest)=splitCount rest+1 := by simp [splitCount,hs]
      rw [hcount]
      nlinarith
    · simpa [refinePiecesExecute,splitCount,hs] using ih history

end EnvyFreeResearch.Full.UpperShrinkCarve
