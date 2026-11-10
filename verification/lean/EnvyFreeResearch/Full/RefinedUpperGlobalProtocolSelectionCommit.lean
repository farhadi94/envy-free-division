import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionData

/-! The finite selected permutation is extended to original agent labels.
Its cached guarantees refer to the actual pending phase after dispatch. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem transferCandidate_commit_cached (p : Pending n) (direction : Direction)
    (alpha : Equiv.Perm (Fin p.anchor.active.card)) (b h : Fin p.anchor.active.card)
    (hv : Selection.Valid (RefinedUpperRepair.nearError n) (p.selectionData direction) (.commit alpha b h)) :
    let next := p.transferCandidate (.commit alpha b h)
    next.anchor.edge direction next.witness next.target ∧
    (∀ i ∈ next.anchor.active, next.snapshotGap direction i (next.permutation i) ≤
      RefinedUpperRepair.nearError n*total next.buffer i) ∧
    2*total next.buffer next.witness ≤ next.snapshotGap direction next.witness (next.permutation next.target) := by
  rcases hv with ⟨hgraph,hown,hlarge⟩
  refine ⟨(localGraph_iff p direction b h).mp hgraph,?_,?_⟩
  · intro i hi
    obtain ⟨j,rfl⟩ := enumerate_preimage p.anchor.active i hi
    change p.snapshotGap direction (enumerate p.anchor.active j)
      (extendPermutation p.anchor.active alpha (enumerate p.anchor.active j)) ≤ _
    rw [extendPermutation_apply]
    exact hown j
  · change 2*total p.buffer (enumerate p.anchor.active b) ≤
      p.snapshotGap direction (enumerate p.anchor.active b)
        (extendPermutation p.anchor.active alpha (enumerate p.anchor.active h))
    rw [extendPermutation_apply]
    exact hlarge

theorem transferCandidate_physical
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
    (c : Selection.Candidate p.anchor.active.card) :
    (p.transferCandidate c).Physical μ whole := by
  cases c with
  | commit alpha b h =>
    exact pending_transfer_physical μ whole p hp _ _ _ (extendPermutation_fixed _ alpha)
  | shrink b h =>
    exact pending_transfer_physical μ whole p hp _ _ _ (fun _ _ => rfl)

theorem transferCandidate_saved_missing
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole) (direction : Direction)
    (c : Selection.Candidate p.anchor.active.card)
    (hv : Selection.Valid (RefinedUpperRepair.nearError n) (p.selectionData direction) c) :
    let next := p.transferCandidate c
    next.witness ∈ next.anchor.active ∧ next.target ∈ next.anchor.active ∧
    next.target ≠ next.witness ∧
    next.target ∉ R4GlobalPotential.targets (margin direction (next.anchor.table μ).value)
      (next.anchor.table μ).residue next.witness := by
  have he : (p.transferCandidate c).anchor.edge direction (p.transferCandidate c).witness
      (p.transferCandidate c).target := by
    cases c with
    | commit alpha b h => exact (localGraph_iff p direction b h).mp hv.1
    | shrink b h => exact (localGraph_iff p direction b h).mp hv.1
  have hn := edge_missing μ whole _ (transferCandidate_physical μ whole p hp c).anchor direction he
  exact ⟨he.1,he.2.1,he.2.2.1,hn⟩

theorem transferCandidate_commit_repair_input [Nonempty (Fin n)]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
    [Nonempty (Fin p.anchor.active.card)] (chores : Bool)
    (alpha : Equiv.Perm (Fin p.anchor.active.card)) (b h : Fin p.anchor.active.card)
    (hv : Selection.Valid (RefinedUpperRepair.nearError n)
      (p.selectionData (if chores then .chore else .cake)) (.commit alpha b h))
    (hW : ActiveEF (if chores then .chore else .cake) (value μ p.anchor.bundles) p.anchor.active)
    (hH : ActiveEF (if chores then .chore else .cake) (value μ p.shrunk) p.anchor.active)
    (hX : ActiveEF (if chores then .chore else .cake) (value μ p.snapshot) p.anchor.active) :
    let next := p.transferCandidate (.commit alpha b h)
    UpperRepairPreparationChecks.Near chores μ (enumerate p.anchor.active) next.buffer
      (fun j => next.endowments (enumerate p.anchor.active j)) (RefinedUpperRepair.nearError n) ∧
    (2-RefinedUpperRepair.nearError n)*(μ next.witness).real (domain next.buffer.cells) ≤
      margin (if chores then .chore else .cake) (value μ next.endowments) next.witness next.target := by
  have hc := transferCandidate_commit_cached p (if chores then .chore else .cake) alpha b h hv
  exact pending_cached_repair_input μ whole _ (transferCandidate_physical μ whole p hp (.commit alpha b h))
    chores (enumerate p.anchor.active) (enumerate_mem _) (RefinedUpperRepair.nearError n)
    hW hH hX hc.2.1 hc.1.1 hc.1.2.1 hc.2.2

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
