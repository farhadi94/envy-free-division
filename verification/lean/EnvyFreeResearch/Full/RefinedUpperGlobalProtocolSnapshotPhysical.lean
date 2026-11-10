import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotAction
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolFacts
import EnvyFreeResearch.Full.UpperPopulationExtensionFacts
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolHistory

/-! Literal accepted Snapshot data become the concrete saved pending state.
The local Snapshot success interface is explicit until connected to its producer. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
  RefinedUpperSnapshotProtocol RefinedUpperRepairProgram GlobalCompletion
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (a : Anchor n) [Nonempty (Fin a.active.card)]
  (hk : 0 < a.active.card) (chores : Bool) (result : PhysicalResult n a.active.card)
  (facts : SnapshotSuccessFacts μ chores (enumerate a.active) a.residue result)

include facts in
theorem snapshot_extension_activeEF :
    ActiveEF (if chores then .chore else .cake)
      (value μ (extendPieces a.active result.1 result.2.1.history)) a.active := by
  apply extendPieces_activeEF μ _ a.active result.1 result.2.1.history
  intro i j
  have h := facts.envyFree i j
  cases chores <;> simp only [Bool.false_eq_true,↓reduceIte,GlobalCompletion.margin] at h ⊢ <;> linarith

include facts in
theorem snapshot_extension_separate (j : Fin n) :
    Disjoint (domain (extendPieces a.active result.1 result.2.1.history j).cells)
      (domain result.2.1.cells) := by
  by_cases hj : j ∈ a.active
  · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
    rw [extendPieces_apply]
    exact facts.residue_disjoint i
  · rw [extendPieces_frozen _ _ _ _ hj]
    exact empty_disjoint _

include facts in
theorem snapshotPending_physical (whole : Set ℝ) (ha : a.Physical μ whole)
    (hh : a.HistoryCompatible) (hext : a.residue.history ⊆ result.2.1.history) :
    (a.snapshotPending hk chores result).Physical μ whole := by
  apply pending_start_physical μ whole a ha _ result.2.1
  · exact extendPieces_wellFormed μ _ _ _ facts.residue_wellFormed.2.2.1 facts.allocation_wellFormed
  · exact facts.residue_wellFormed
  · exact extendPieces_pairwise _ _ _ facts.allocation_disjoint
  · exact snapshot_extension_separate μ a chores result facts
  · rw [extendPieces_domain]
    exact facts.material_preserved
  · intro j x hx
    exact hext (hh j hx)
  · intro j
    rw [extendPieces_history _ _ _ facts.common_history]
  · intro j hj
    rw [extendPieces_frozen _ _ _ _ hj]
    rfl

include facts in
theorem snapshotPending_snapshot_activeEF :
    ActiveEF (if chores then .chore else .cake)
      (value μ (a.snapshotPending hk chores result).snapshot) a.active :=
  snapshot_extension_activeEF μ a chores result facts

theorem snapshotPending_shrunk_activeEF :
    ActiveEF (if chores then .chore else .cake)
      (value μ (a.snapshotPending hk chores result).shrunk) a.active := by
  intro i hi j hj
  cases chores <;> simp [Anchor.snapshotPending,Pending.start,value,empty,domain,GlobalCompletion.margin]

include facts in
theorem snapshot_terminal (whole : Set ℝ) (ha : a.Committed μ (if chores then .chore else .cake) whole)
    (hh : a.HistoryCompatible) (hext : a.residue.history ⊆ result.2.1.history)
    (hdone : result.2.1.cells=[]) :
    (terminal a (extendPieces a.active result.1 result.2.1.history) result.2.1.history).Committed μ
      (if chores then .chore else .cake) whole ∧
    (⋃ j, domain ((terminal a (extendPieces a.active result.1 result.2.1.history) result.2.1.history).bundles j).cells)=whole ∧
    (terminal a (extendPieces a.active result.1 result.2.1.history) result.2.1.history).HistoryCompatible := by
  have hw := extendPieces_wellFormed μ a.active result.1 result.2.1.history
    facts.residue_wellFormed.2.2.1 facts.allocation_wellFormed
  have hpair := extendPieces_pairwise a.active result.1 result.2.1.history facts.allocation_disjoint
  have hcover : (⋃ j, domain (extendPieces a.active result.1 result.2.1.history j).cells)=domain a.residue.cells := by
    rw [extendPieces_domain]
    simpa only [hdone,domain,union_empty] using facts.material_preserved
  have hfrozen : ∀ j ∉ a.active, domain (extendPieces a.active result.1 result.2.1.history j).cells=∅ := by
    intro j hj
    rw [extendPieces_frozen _ _ _ _ hj]
    rfl
  have hold : ∀ j, (a.bundles j).history ⊆ result.2.1.history := fun j _ hx => hext (hh j hx)
  have hadd : ∀ j, (extendPieces a.active result.1 result.2.1.history j).history ⊆ result.2.1.history := by
    intro j
    rw [extendPieces_history _ _ _ facts.common_history]
  have hef := snapshot_extension_activeEF μ a chores result facts
  exact ⟨terminal_committed μ _ whole a ha _ _ facts.residue_wellFormed.2.2.1 hw hpair hcover hfrozen hold hadd hef,
    terminal_complete μ _ whole a ha _ _ facts.residue_wellFormed.2.2.1 hw hpair hcover hfrozen hold hadd hef,
    commit_history _ _ _ _⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
