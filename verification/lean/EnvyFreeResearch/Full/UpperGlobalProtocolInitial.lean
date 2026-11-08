import EnvyFreeResearch.Full.UpperGlobalPhysical
import EnvyFreeResearch.Full.UpperComponentGroups

/-! Initial physical anchor and its all-observer global invariant. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

def initial (origin : State n) : Anchor n where
  bundles _ := empty origin.history
  residue := origin
  active := Finset.univ

theorem initial_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (origin : State n) (hgood : WellFormed μ origin) :
    (initial origin).Physical μ (domain origin.cells) := by
  refine ⟨fun _ => empty_wellFormed μ _ hgood.2.2.1,hgood,?_,?_,?_⟩
  · intro i j hij
    simp [initial,empty,domain]
  · intro j
    simp [initial,empty,domain]
  · simp [initial,empty,domain]

theorem initial_committed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (direction : GlobalCompletion.Direction)
    (origin : State n) (hgood : WellFormed μ origin) :
    (initial origin).Committed μ direction (domain origin.cells) := by
  refine ⟨initial_physical μ origin hgood,?_⟩
  have h := GlobalCompletion.initial_state_valid direction
    (fun i : Fin n => (μ i).real (domain origin.cells)) (fun _ => measureReal_nonneg)
  have hv : value μ (initial origin).bundles = fun _ _ => 0 := by
    funext i j
    simp [value,initial,empty,domain]
  unfold Anchor.table
  rw [hv]
  simpa only [initial,Finset.coe_univ] using h

end EnvyFreeResearch.Full.UpperGlobalPhysical
