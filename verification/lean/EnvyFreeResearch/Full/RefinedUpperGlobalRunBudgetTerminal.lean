import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetPotential

/-! Completed physical allocations saturate the actual cached potential.
Refreshing only the history preserves that potential on truthful caches. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ)

theorem completed_residue_empty (a : Anchor n) (ha : a.Physical μ whole)
    (hcomplete : (⋃ j, domain (a.bundles j).cells)=whole) : domain a.residue.cells=∅ := by
  have hd : Disjoint (⋃ j, domain (a.bundles j).cells) (domain a.residue.cells) :=
    disjoint_iUnion_left.mpr ha.separate
  rw [hcomplete] at hd
  have hs : domain a.residue.cells ⊆ whole := by rw [← ha.cover]; exact subset_union_right
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact disjoint_left.mp hd (hs hx) hx

theorem committed_complete_saturated (a : Anchor n) (direction : Direction)
    (ha : a.Committed μ direction whole)
    (hcomplete : (⋃ j, domain (a.bundles j).cells)=whole) :
    a.cachedPotential direction = n*(n-1) := by
  rw [cachedPotential_correct μ whole a ha.1]
  have hz := completed_residue_empty μ whole a ha.1 hcomplete
  have hr : ∀ i, (a.table μ).residue i=0 := by
    intro i
    change (μ i).real (domain a.residue.cells)=0
    rw [hz,measureReal_empty]
  simpa only [statePotential,dominationPotential,Fintype.card_fin] using
    R4GlobalPotential.zero_residue_potential (margin direction (a.table μ).value)
      (a.table μ).residue ha.2.2.2.1 hr

theorem valid_done_saturated (chores : Bool) (a : Anchor n)
    (hv : (Phase.done a).Valid μ chores whole) :
    a.cachedPotential (if chores then .chore else .cake) = n*(n-1) :=
  committed_complete_saturated μ whole a _ hv.1 hv.2.2

theorem refreshed_potential (a : Anchor n) (direction : Direction)
    (history : UpperCircularStage.History n)
    (ha : a.Physical μ whole) (hb : (refresh a history).Physical μ whole) :
    (refresh a history).cachedPotential direction=a.cachedPotential direction := by
  rw [cachedPotential_correct μ whole _ hb,cachedPotential_correct μ whole _ ha]
  rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
