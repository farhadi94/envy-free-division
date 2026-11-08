import EnvyFreeResearch.Full.UpperShrinkCarvePhysicalRounds
import EnvyFreeResearch.Full.UpperShrinkCarveMomentRefinement
import EnvyFreeResearch.Full.UpperShrinkCarveMomentFloating
import EnvyFreeResearch.Full.UpperShrinkCarveDecay

/-! Iteration invariants for the concrete carving executor. The exact
moments and geometric decay follow at every round of the actual program. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

variable {n k : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (normal : Fin k → ℝ)

include hp in
theorem rounds_moment (J : ℕ) (mesh : Mesh n k) (U : Set ℝ)
    (hphy : mesh.Physical μ U) (hv : mesh.FractionsValid) (hn : ∀ i, normal i ≠ 0)
    (i j : Fin k) :
    moment (μ (active i)) (roundsExecute policy active normal J mesh).pieces j =
      moment (μ (active i)) mesh.pieces j := by
  induction J generalizing mesh with
  | zero => exact floated_moment μ active normal mesh hphy.pieces hv hn i j
  | succ J ih =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    have hr := floated_physical μ active normal mesh U hphy
    have hrv := (floated_valid_count active normal mesh hv).1
    have hnphy := refinePieces_physical μ policy hp active ready.pieces ready.history hr.truthful hr.pieces hr.disjoint
    rw [hr.cover] at hnphy
    have hnv := refinement_valid policy active ready.pieces ready.history hrv
    change moment (μ (active i)) (roundsExecute policy active normal J next).pieces j = _
    rw [ih next hnphy hnv]
    change moment (μ (active i)) (refinePiecesExecute policy active ready.pieces ready.history).pieces j = _
    rw [refinePieces_moment μ policy hp active _ _ hr.pieces]
    exact floated_moment μ active normal mesh hphy.pieces hv hn i j

include hp in
theorem rounds_split_bound (J : ℕ) (mesh : Mesh n k) (U : Set ℝ)
    (hphy : mesh.Physical μ U) (hv : mesh.FractionsValid) (bound : Fin k → ℝ)
    (hb : SplitBound μ active bound mesh.pieces) :
    SplitBound μ active (fun i => bound i/2^J) (roundsExecute policy active normal J mesh).pieces := by
  induction J generalizing mesh bound with
  | zero =>
    intro p hm hs i
    simpa only [pow_zero,div_one] using floated_split_bound μ active normal bound mesh hv hb p hm hs i
  | succ J ih =>
    let ready := floated active normal mesh
    let next := refinePiecesExecute policy active ready.pieces ready.history
    have hr := floated_physical μ active normal mesh U hphy
    have hrv := (floated_valid_count active normal mesh hv).1
    have hnphy := refinePieces_physical μ policy hp active ready.pieces ready.history hr.truthful hr.pieces hr.disjoint
    rw [hr.cover] at hnphy
    have hnv := refinement_valid policy active ready.pieces ready.history hrv
    have hrb := floated_split_bound μ active normal bound mesh hv hb
    have hnb := refinement_split_halving μ policy hp active bound _ _ hr.pieces hrb
    have hlast := ih next hnphy hnv (fun i => bound i/2) hnb
    intro p hmem hs i
    have h := hlast p hmem hs i
    convert h using 1
    change bound i/2^(J+1)=bound i/2/2^J
    rw [div_div,pow_succ]
    ring

end EnvyFreeResearch.Full.UpperShrinkCarve
