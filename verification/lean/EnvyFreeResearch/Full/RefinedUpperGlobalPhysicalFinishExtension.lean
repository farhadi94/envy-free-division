import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalPending
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalReceivedInvariant
import EnvyFreeResearch.Full.UpperPopulationExtension

/-! Extending actual local Repair output retains every frozen original bundle.
The added family is a physical union, not a reconstructed complement cache. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
variable {n : ℕ}

def output (p : Pending n) (localOutput : Fin p.anchor.active.card → State n) (j : Fin n) : State n :=
  if hj : j ∈ p.anchor.active then
    localOutput ((p.anchor.active.orderIsoOfFin rfl).symm ⟨j,hj⟩)
  else p.anchor.bundles j

theorem output_active (p : Pending n) (localOutput : Fin p.anchor.active.card → State n)
    (i : Fin p.anchor.active.card) : output p localOutput (enumerate p.anchor.active i) = localOutput i := by
  rw [output,dif_pos (UpperZeroRows.enumerate_mem _ _)]
  exact congrArg localOutput ((p.anchor.active.orderIsoOfFin rfl).symm_apply_apply i)

theorem output_frozen (p : Pending n) (localOutput : Fin p.anchor.active.card → State n)
    (j : Fin n) (hj : j ∉ p.anchor.active) : output p localOutput j = p.anchor.bundles j := by
  simp [output,hj]

def added (p : Pending n) (localAdded : Fin p.anchor.active.card → State n)
    (history : UpperCircularStage.History n) (j : Fin n) : State n :=
  join (p.additions j) (extendPieces p.anchor.active localAdded history j) history

theorem added_domain (p : Pending n) (localAdded : Fin p.anchor.active.card → State n)
    (history : UpperCircularStage.History n) (j : Fin n) :
    domain (added p localAdded history j).cells = domain (p.additions j).cells ∪
      domain (extendPieces p.anchor.active localAdded history j).cells := join_domain _ _ _

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
include hp

theorem output_wellFormed (localOutput : Fin p.anchor.active.card → State n)
    (hlocal : ∀ i, WellFormed μ (localOutput i)) : ∀ j, WellFormed μ (output p localOutput j) := by
  intro j
  unfold output
  split_ifs
  · exact hlocal _
  · exact hp.anchor.bundles_wellFormed j

theorem added_frozen (localAdded : Fin p.anchor.active.card → State n)
    (history : UpperCircularStage.History n) (j : Fin n) (hj : j ∉ p.anchor.active) :
    domain (added p localAdded history j).cells = ∅ := by
  rw [added_domain,pending_additions_frozen μ whole p hp j hj,extendPieces_frozen _ _ _ _ hj]
  exact empty_union _

theorem output_whole_label (localOutput localAdded : Fin p.anchor.active.card → State n)
    (history : UpperCircularStage.History n) (f : Equiv.Perm (Fin p.anchor.active.card))
    (hl : ∀ i, domain (localOutput (f i)).cells =
      domain (p.endowments (enumerate p.anchor.active i)).cells ∪ domain (localAdded i).cells) :
    ∀ j, domain (output p localOutput (extendPermutation p.anchor.active f j)).cells =
      domain (p.anchor.bundles j).cells ∪ domain (added p localAdded history j).cells := by
  intro j
  by_cases hj : j ∈ p.anchor.active
  · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
    rw [extendPermutation_apply,output_active,hl,added_domain,extendPieces_apply]
    simp only [Pending.endowments,Pending.additions,join_domain,union_assoc]
  · rw [extendPermutation_fixed _ _ _ hj,output_frozen _ _ _ hj,
      added_frozen μ whole p hp _ _ _ hj,union_empty]

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalFinish
