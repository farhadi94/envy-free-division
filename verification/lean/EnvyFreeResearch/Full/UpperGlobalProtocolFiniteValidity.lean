import EnvyFreeResearch.Full.UpperGlobalProtocolCorrectness

/-! Validity for every finite tape prefix, before passing to its state law. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape
variable {n : ℕ}

theorem finiteRun_valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (t : ℕ) (draws : Fin t → Universal n) :
    (UpperGlobalRun.finiteRun (Phase.step policy fallback chores) initial t draws).Valid μ chores whole := by
  induction t with
  | zero => exact hinit
  | succ t ih =>
    exact step_valid μ whole chores _ (ih (fun i => draws i.castSucc)) policy hpolicy fallback (draws (Fin.last t))

end EnvyFreeResearch.Full.UpperGlobalPhysical
