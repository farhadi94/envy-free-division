import EnvyFreeResearch.Full.UpperShrinkCarveExecution

/-! Separate ordinary Cut accounting for the actual refinement pass. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperCircularStage

def cuts (history : History n) : ℕ := (history.map Prod.fst).countP isCut

theorem medianChain_cut_bound (policy : Policy n) (cutters : List (Fin n)) (state : State n) :
    cuts (medianChainExecute policy cutters state).history ≤ cuts state.history + cutters.length := by
  induction cutters generalizing state with
  | nil => simp [medianChainExecute]
  | cons i rest ih =>
    have h := ih (UpperShrink.median policy state i).2
    have hf := UpperShrink.median_cut_bound policy state i
    change cuts (UpperShrink.median policy state i).2.history ≤ cuts state.history+1 at hf
    simp only [medianChainExecute,List.length_cons]
    omega

theorem refinePieces_cut_bound (policy : Policy n) (active : Fin k → Fin n)
    (pieces : List (Piece k)) (history : History n) :
    cuts (refinePiecesExecute policy active pieces history).history ≤ cuts history + splitCount pieces*k := by
  induction pieces generalizing history with
  | nil => simp [refinePiecesExecute,splitCount]
  | cons piece rest ih =>
    by_cases hs : split piece
    · have hf := medianChain_cut_bound policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)
      have ht := ih (medianChainExecute policy (List.ofFn active) (⟨piece.cells,history⟩ : State n)).history
      simp only [List.length_ofFn] at hf
      simp only [refinePiecesExecute,hs,ite_true]
      have hcount : splitCount (piece::rest)=splitCount rest+1 := by simp [splitCount,hs]
      rw [hcount,Nat.add_mul,Nat.one_mul]
      omega
    · simpa [refinePiecesExecute,splitCount,hs] using ih history

end EnvyFreeResearch.Full.UpperShrinkCarve
