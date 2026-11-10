import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeKernel
import EnvyFreeResearch.Full.RefinedUpperGlobalNormalizeProgram

/-! The actual dispatcher yields either a complete allocation or the exact
positive strongly-connected anchor required for the next Snapshot call. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

def Normalized (chores : Bool) (whole : Set ℝ) : Phase n → Prop
  | .done a => a.Committed μ (direction chores) whole ∧ a.HistoryCompatible ∧
      (⋃ j, domain (a.bundles j).cells)=whole
  | .snapshot a => a.Committed μ (direction chores) whole ∧ a.HistoryCompatible ∧
      3 ≤ a.active.card ∧ positive a ∧ RefinedUpperGlobal.Sink.StrongOn (a.edge (direction chores)) a.active
  | _ => False

theorem request_execute_valid (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (chores : Bool) (whole : Set ℝ) (request : Request n) (hv : request.Valid μ chores whole) :
    Normalized μ chores whole (requestExecute policy chores request) := by
  cases request with
  | done a => exact hv
  | snapshot a => exact hv
  | two a cutter chooser =>
    obtain ⟨ha,hh,hactive,hne,hpos⟩ := hv
    have ht := twoAgent_terminal μ policy hp chores whole a ha hh cutter chooser hactive hne hpos
    exact ⟨ht.1,terminal_history _ _ _,ht.2⟩

theorem execute_valid (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (chores : Bool) (whole : Set ℝ) (a : Anchor n)
    (ha : a.Committed μ (direction chores) whole) (hh : a.HistoryCompatible) (hn : a.active.Nonempty) :
    Normalized μ chores whole (execute policy fallback chores a) :=
  request_execute_valid μ policy hp chores whole _
    (normalize_valid μ fallback chores n whole a ha hh hn (UpperZeroRows.active_size_bound _))

theorem Normalized.committed {chores : Bool} {whole : Set ℝ} {phase : Phase n}
    (h : Normalized μ chores whole phase) : phase.anchor.Committed μ (direction chores) whole := by
  cases phase <;> first | exact h.1 | exact h.elim

theorem Normalized.history {chores : Bool} {whole : Set ℝ} {phase : Phase n}
    (h : Normalized μ chores whole phase) : phase.anchor.HistoryCompatible := by
  cases phase <;> first | exact h.2.1 | exact h.elim

end EnvyFreeResearch.Full.RefinedUpperGlobalNormalize
