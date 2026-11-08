import EnvyFreeResearch.Full.UpperShrinkCarvePhysicalRefinement
import EnvyFreeResearch.Full.UpperShrinkCarvePhysicalMesh
import EnvyFreeResearch.Full.UpperShrinkCarveRounds

noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

variable {n k : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (policy : Policy n)
  (hp : Admissible (Chores.measureProfile μ) policy)

include hp in
theorem rounds_physical (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (mesh : Mesh n k) (U : Set ℝ) (h : mesh.Physical μ U) :
    (roundsExecute policy active normal J mesh).Physical μ U := by
  induction J generalizing mesh with
  | zero => exact floated_physical μ active normal mesh U h
  | succ J ih =>
    let ready := floated active normal mesh
    have hr := floated_physical μ active normal mesh U h
    have hn := refinePieces_physical μ policy hp active ready.pieces ready.history
      hr.truthful hr.pieces hr.disjoint
    rw [hr.cover] at hn
    exact ih _ hn

end EnvyFreeResearch.Full.UpperShrinkCarve
