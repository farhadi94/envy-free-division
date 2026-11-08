import EnvyFreeResearch.Full.UpperGlobalPhysical

/-! The saved-anchor nondomination graph is computed from recorded cache
entries, with no additional valuation access. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ}

def Anchor.cachedValue (a : Anchor n) : GlobalCompletion.Table (Fin n) :=
  fun i j => total (a.bundles j) i

def Anchor.cachedResidue (a : Anchor n) : Fin n → ℝ := total a.residue

def Anchor.edge (a : Anchor n) (direction : GlobalCompletion.Direction) (i j : Fin n) : Prop :=
  i ∈ a.active ∧ j ∈ a.active ∧ j ≠ i ∧
    GlobalCompletion.margin direction a.cachedValue i j < a.cachedResidue i

def Anchor.cachedPotential (a : Anchor n) (direction : GlobalCompletion.Direction) : ℕ :=
  GlobalCompletion.dominationPotential direction a.cachedValue a.cachedResidue

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n) (ha : a.Physical μ whole)
include ha

theorem cachedValue_correct : a.cachedValue = (a.table μ).value := by
  funext i j
  exact total_correct μ (a.bundles j) (ha.bundles_wellFormed j) i

theorem cachedResidue_correct : a.cachedResidue = (a.table μ).residue := by
  funext i
  exact total_correct μ a.residue ha.residue_wellFormed i

theorem edge_iff (direction : GlobalCompletion.Direction) (i j : Fin n) :
    a.edge direction i j ↔ i ∈ a.active ∧ j ∈ a.active ∧ j ≠ i ∧
      GlobalCompletion.margin direction (a.table μ).value i j < (a.table μ).residue i := by
  unfold Anchor.edge
  rw [cachedValue_correct μ whole a ha,cachedResidue_correct μ whole a ha]

theorem cachedPotential_correct (direction : GlobalCompletion.Direction) :
    a.cachedPotential direction = GlobalCompletion.statePotential direction (a.table μ) := by
  unfold Anchor.cachedPotential GlobalCompletion.statePotential
  rw [cachedValue_correct μ whole a ha,cachedResidue_correct μ whole a ha]

theorem edge_missing (direction : GlobalCompletion.Direction) {i j : Fin n}
    (hedge : a.edge direction i j) :
    j ∉ R4GlobalPotential.targets (GlobalCompletion.margin direction (a.table μ).value)
      (a.table μ).residue i := by
  have h := (edge_iff μ whole a ha direction i j).mp hedge
  simp only [R4GlobalPotential.targets,Finset.mem_filter,Finset.mem_univ,true_and,not_and]
  intro _
  exact not_le_of_gt h.2.2.2

end EnvyFreeResearch.Full.UpperGlobalPhysical
