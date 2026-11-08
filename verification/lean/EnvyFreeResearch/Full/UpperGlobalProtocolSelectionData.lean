import EnvyFreeResearch.Full.UpperGlobalProtocolShrink
import EnvyFreeResearch.Full.UpperGlobalProtocolTransferSelectionSound
import EnvyFreeResearch.Full.UpperGlobalProtocolTransferSelectionDispatcher
import EnvyFreeResearch.Full.UpperGlobalProtocolTransferBounds
import EnvyFreeResearch.Full.UpperGlobalPendingMassReady

/-! The transfer search reads the actual saved anchor graph, Snapshot cache,
and current residue cache. No valuation queries are used by these decisions. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open UpperGlobal.Transfer
variable {n : ℕ}

def activeIndex (active : Finset (Fin n)) [Nonempty (Fin active.card)] (j : Fin n) : Fin active.card :=
  if hj : j ∈ active then (active.orderIsoOfFin rfl).symm ⟨j,hj⟩ else Classical.arbitrary _

theorem activeIndex_apply (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (i : Fin active.card) : activeIndex active (enumerate active i)=i := by
  rw [activeIndex,dif_pos (enumerate_mem active i)]
  exact (active.orderIsoOfFin rfl).symm_apply_apply i

theorem enumerate_activeIndex (active : Finset (Fin n)) [Nonempty (Fin active.card)]
    (j : Fin n) (hj : j ∈ active) : enumerate active (activeIndex active j)=j := by
  obtain ⟨i,rfl⟩ := enumerate_preimage active j hj
  rw [activeIndex_apply]

def Pending.snapshotGap (p : Pending n) (direction : Direction) (i j : Fin n) : ℝ :=
  margin direction (fun a b => total (p.snapshot b) a) i j

def Pending.localGraph (p : Pending n) (direction : Direction) :
    Fin p.anchor.active.card → Fin p.anchor.active.card → Bool :=
  fun i j => decide (p.anchor.edge direction (enumerate p.anchor.active i) (enumerate p.anchor.active j))

def Pending.localGap (p : Pending n) (direction : Direction) :
    Fin p.anchor.active.card → Fin p.anchor.active.card → ℝ :=
  fun i j => p.snapshotGap direction (enumerate p.anchor.active i) (enumerate p.anchor.active j)

def Pending.localBuffer (p : Pending n) : Fin p.anchor.active.card → ℝ :=
  fun i => total p.buffer (enumerate p.anchor.active i)

def Pending.selectionData (p : Pending n) (direction : Direction) : Selection.CachedData p.anchor.active.card :=
  (p.localGraph direction,p.localGap direction,p.localBuffer)

def Pending.firstFactor (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (direction : Direction) : ℝ :=
  factor (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
    (factorIndex (UpperShrinkPrecision.theta n) (UpperRepair.nearError n)
      (fun i => p.localGap direction i (activeIndex p.anchor.active p.target)/p.localBuffer i)
      (activeIndex p.anchor.active p.target)).val

def Pending.selectTransfer (p : Pending n) (direction : Direction) :
    Option (Selection.Candidate p.anchor.active.card) :=
  Selection.select (UpperRepair.nearError n) (p.selectionData direction)

def Pending.transferCandidate (p : Pending n) : Selection.Candidate p.anchor.active.card → Pending n
  | .commit alpha b h => p.transfer (extendPermutation p.anchor.active alpha)
      (enumerate p.anchor.active b) (enumerate p.anchor.active h)
  | .shrink b h => p.transfer (Equiv.refl _) (enumerate p.anchor.active b) (enumerate p.anchor.active h)

def Pending.dispatchTransfer (p : Pending n) : Selection.Candidate p.anchor.active.card → Phase n
  | c@(.commit _ _ _) => .finalRepair (p.transferCandidate c)
  | c@(.shrink _ _) => .secondShrink (p.transferCandidate c)

theorem localGraph_iff (p : Pending n) (direction : Direction) (i j : Fin p.anchor.active.card) :
    p.localGraph direction i j=true ↔
      p.anchor.edge direction (enumerate p.anchor.active i) (enumerate p.anchor.active j) := by
  simp [Pending.localGraph]

theorem localGap_self (p : Pending n) (direction : Direction) (i : Fin p.anchor.active.card) :
    p.localGap direction i i=0 := GlobalCompletion.margin_self direction (fun a b => total (p.snapshot b) a) _

theorem localGap_addShrink (p : Pending n) (direction : Direction) (pieces : Fin n → State n)
    (residue : State n) : (p.addShrink pieces residue).localGap direction=p.localGap direction := rfl

theorem localGraph_addShrink (p : Pending n) (direction : Direction) (pieces : Fin n → State n)
    (residue : State n) : (p.addShrink pieces residue).localGraph direction=p.localGraph direction := rfl

end EnvyFreeResearch.Full.UpperGlobalPhysical
