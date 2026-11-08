import EnvyFreeResearch.Full.UpperShrinkCarveMedianChain
import EnvyFreeResearch.Full.UpperShrinkCarveRefinement

/-! Semantic real-color moments of the actual list of logical pieces.
Replacing a queried parent by its physical components with inherited colors
preserves every original observer's moment exactly. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

def moment (μ : Measure ℝ) (pieces : List (Piece k)) (j : Fin k) : ℝ :=
  (pieces.map (fun p => μ.real (domain p.cells)*p.fraction (some j))).sum

@[simp] theorem moment_nil (μ : Measure ℝ) (j : Fin k) : moment μ [] j = 0 := rfl

@[simp] theorem moment_cons (μ : Measure ℝ) (p : Piece k) (rest : List (Piece k)) (j : Fin k) :
    moment μ (p::rest) j = μ.real (domain p.cells)*p.fraction (some j)+moment μ rest j := rfl

@[simp] theorem moment_append (μ : Measure ℝ) (as bs : List (Piece k)) (j : Fin k) :
    moment μ (as++bs) j = moment μ as j+moment μ bs j := by simp [moment]

theorem children_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p : Piece k) (state : State n) (hdis : DisjointComponents state.cells) (j : Fin k) :
    moment μ (children p state) j = μ.real (domain state.cells)*p.fraction (some j) := by
  simp only [moment,children,List.map_map,Function.comp_def,domain,union_empty]
  rw [List.sum_map_mul_right]
  congr 1
  exact (domain_mass_sum μ state.cells hdis).symm

theorem median_children_moment (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (p : Piece k) (history : History n) (cutters : List (Fin n))
    (hs : WellFormed μ (⟨p.cells,history⟩ : State n)) (i : Fin n) (j : Fin k) :
    moment (μ i) (children p (medianChainExecute policy cutters ⟨p.cells,history⟩)) j =
      (μ i).real (domain p.cells)*p.fraction (some j) := by
  have hf := medianChain_wellFormed μ policy hp cutters (⟨p.cells,history⟩ : State n) hs
  rw [children_moment (μ i) p _ hf.2.1,medianChain_domain]

theorem moment_ofFn (μ : Measure ℝ) (p : Fin r → Piece k) (j : Fin k) :
    moment μ (List.ofFn p) j = ∑ e, μ.real (domain (p e).cells)*(p e).fraction (some j) := by
  rw [moment,List.map_ofFn,List.sum_ofFn]
  rfl

end EnvyFreeResearch.Full.UpperShrinkCarve
