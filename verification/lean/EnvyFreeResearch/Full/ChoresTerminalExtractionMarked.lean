import EnvyFreeResearch.Full.ChoresOuterPrivateTerminal
import EnvyFreeResearch.Full.ChoresOuterResidueRemoval
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! The atomic extracted union is exactly the marked actual donor slots
of the terminal private cache, including affine-zero assignments. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ChoreComposition
open ComponentDonors ComponentExtraction
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (A : Finset (Fin n))
  (out : ComponentClosed.Result (Root := Fin data.size) A)

def extractedSlots : Finset (RootId × Fin n) :=
  Finset.univ.image (fun j : A => ((data.frames (out.allocation.assigned j)).root,
    data.pending.partition.representative (j : Fin n)))

theorem terminal_private_donor_slot
    (oldPrivate : RootId → Fin n → List (Parent n))
    (hinj : Function.Injective (fun s => (data.frames s).root)) (j : A) :
    Outer.terminalPrivateCache data original A out oldPrivate
      (data.frames (out.allocation.assigned j)).root
      (data.pending.partition.representative (j : Fin n))=(out.parts j).suffixParts := by
  unfold Outer.terminalPrivateCache
  rw [ComponentPhysical.patch_live data.frames oldPrivate _ hinj]
  unfold Outer.closedPrivateCache
  rw [ComponentAssignment.dispatch_assigned]
  simp only [ComponentPieces.proposalResidueCache,affine,affineProposal,ite_true]

theorem marked_private_eq_extracted
    (oldPrivate : RootId → Fin n → List (Parent n))
    (hinj : Function.Injective (fun s => (data.frames s).root)) :
    Outer.markedPrivate (Outer.terminalPrivateCache data original A out oldPrivate)
      (extractedSlots data A out)=extracted out := by
  ext x
  simp only [Outer.markedPrivate,extracted,mem_iUnion]
  constructor
  · rintro ⟨slot,hslot,hx⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hslot
    exact ⟨j,by simpa only [terminal_private_donor_slot data original A out oldPrivate hinj j] using hx⟩
  · rintro ⟨j,hx⟩
    refine ⟨((data.frames (out.allocation.assigned j)).root,
      data.pending.partition.representative (j : Fin n)),?_,?_⟩
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · simpa only [terminal_private_donor_slot data original A out oldPrivate hinj j] using hx

end EnvyFreeResearch.Full.Chores.Terminal
