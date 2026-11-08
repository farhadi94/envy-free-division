import EnvyFreeResearch.Full.UpperShrinkCarveMoments
import EnvyFreeResearch.Full.UpperShrinkCarvePhysical

/-! Exact preservation of the semantic color moments by the actual queried
refinement, including the full history accumulated while processing parents. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

theorem refinePieces_moment (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (pieces : List (Piece k)) (history : History n)
    (hw : ∀ p ∈ pieces, WellFormed μ (⟨p.cells,history⟩ : State n)) (i : Fin n) (j : Fin k) :
    moment (μ i) (refinePiecesExecute policy active pieces history).pieces j =
      moment (μ i) pieces j := by
  induction pieces generalizing history with
  | nil => rfl
  | cons p rest ih =>
    have hpw := hw p (by simp)
    have hrest : ∀ q ∈ rest, WellFormed μ (⟨q.cells,history⟩ : State n) :=
      fun q hq => hw q (by simp [hq])
    by_cases hs : split p
    · let out := medianChainExecute policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have how : WellFormed μ out := medianChain_wellFormed μ policy hp _ _ hpw
      obtain ⟨trace,_,hh⟩ := medianChain_executes policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have he : history ⊆ out.history := by rw [hh]; exact List.subset_append_left _ _
      have hrest' : ∀ q ∈ rest, WellFormed μ (⟨q.cells,out.history⟩ : State n) :=
        fun q hq => wellFormed_history_extend μ _ history out.history (hrest q hq) how.2.2.1 he
      simp only [refinePiecesExecute,hs,ite_true,moment_append,moment_cons]
      rw [ih out.history hrest',median_children_moment μ policy hp p history _ hpw i j]
    · simpa only [refinePiecesExecute,hs,ite_false,moment_cons] using
        congrArg (fun x => (μ i).real (domain p.cells)*p.fraction (some j)+x) (ih history hrest)

end EnvyFreeResearch.Full.UpperShrinkCarve
