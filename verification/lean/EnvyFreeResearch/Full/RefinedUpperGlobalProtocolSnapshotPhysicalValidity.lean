import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotPhysicalMargin
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidity

/-! Phase-invariant preservation by the concrete Snapshot handler. Accepted
local facts and all-attempt history truth remain explicit producer obligations. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows RefinedUpperRepairProgram
  RefinedUpperSnapshotProtocol UpperEndpointCache UpperCircularStage GlobalCompletion
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (a : Anchor n) [Nonempty (Fin a.active.card)]
  (hk : 0 < a.active.card) (chores : Bool) (whole : Set ℝ)
  (ha : Phase.Valid μ chores whole (.snapshot a))

include ha in
theorem refresh_snapshot_valid (history : History n) (ht : Truthful μ history)
    (hext : a.residue.history ⊆ history) : Phase.Valid μ chores whole (.snapshot (refresh a history)) := by
  have hphy := refresh_physical μ whole a ha.1.1 history ht hext
  have hcache : total (refresh a history).residue = total a.residue := by
    funext i
    rw [total_correct μ _ hphy.residue_wellFormed,total_correct μ _ ha.1.1.residue_wellFormed]
    rfl
  have hedge : (refresh a history).edge (if chores then .chore else .cake) =
      a.edge (if chores then .chore else .cake) := by
    funext i j
    simp only [Anchor.edge,Anchor.cachedValue,Anchor.cachedResidue]
    rw [hcache]
    rfl
  refine ⟨refresh_committed μ _ whole a ha.1 history ht hext,
    refresh_history a history ha.2.1 hext,ha.2.2.1,?_,?_⟩
  · intro i hi
    rw [hcache]
    exact ha.2.2.2.1 i hi
  · change RefinedUpperGlobal.Sink.StrongOn ((refresh a history).edge (if chores then .chore else .cake)) a.active
    rw [hedge]
    exact ha.2.2.2.2

include ha in
theorem finishSnapshot_accepted_valid (result : PhysicalResult n a.active.card)
    (facts : SnapshotSuccessFacts μ chores (enumerate a.active) a.residue result)
    (hext : a.residue.history ⊆ result.2.1.history) (haccept : result.2.2=false) :
    Phase.Valid μ chores whole (a.finishSnapshot hk chores result) := by
  by_cases hd : result.2.1.cells=[]
  · have ht := snapshot_terminal μ a chores result facts whole ha.1 ha.2.1 hext hd
    simp only [Anchor.finishSnapshot,haccept,Bool.false_eq_true,ite_false,hd,ite_true,Phase.Valid,
      RefinedUpperGlobalNormalize.Normalized]
    exact ⟨ht.1,ht.2.2,ht.2.1⟩
  · let p := a.snapshotPending hk chores result
    letI : Nonempty (Fin p.anchor.active.card) := inferInstanceAs (Nonempty (Fin a.active.card))
    have hphy : p.Physical μ whole := snapshotPending_physical μ a hk chores result facts whole ha.1.1 ha.2.1 hext
    have hselected := snapshotPending_selected μ a hk chores result facts haccept hd
    have hb : p.Basic μ chores whole := {
      physical := hphy
      anchor_valid := ha.1.2
      population := ha.2.2.1
      snapshot_ef := snapshotPending_snapshot_activeEF μ a hk chores result facts
      shrunk_ef := snapshotPending_shrunk_activeEF μ a hk chores result
      positive := by
        intro i hi
        rw [total_correct μ _ hphy.buffer_wf]
        exact snapshotPending_positive_active μ a hk chores result facts hd i hi
      strong := ha.2.2.2.2 }
    simp only [Anchor.finishSnapshot,haccept,Bool.false_eq_true,ite_false,hd,Phase.Valid]
    change p.FirstReady μ chores whole (p.firstFactor (if chores then .chore else .cake))
    exact {
      toBasic := hb
      permutation_identity := rfl
      witness_active := hselected.1
      target_active := hselected.2.1
      certificate := hselected.2.2.2.2
      factor_eq := fun _ => rfl }

include ha in
theorem finishSnapshot_valid (result : PhysicalResult n a.active.card)
    (htruth : Truthful μ result.2.1.history) (hext : a.residue.history ⊆ result.2.1.history)
    (haccepted : result.2.2=false → SnapshotSuccessFacts μ chores (enumerate a.active) a.residue result) :
    Phase.Valid μ chores whole (a.finishSnapshot hk chores result) := by
  by_cases hs : result.2.2=true
  · simp only [Anchor.finishSnapshot,hs,ite_true]
    exact refresh_snapshot_valid μ a chores whole ha _ htruth hext
  · have hf : result.2.2=false := Bool.eq_false_iff.mpr hs
    exact finishSnapshot_accepted_valid μ a hk chores whole ha result (haccepted hf) hext hf

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
