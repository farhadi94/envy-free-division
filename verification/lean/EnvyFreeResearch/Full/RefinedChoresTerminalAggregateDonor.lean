import EnvyFreeResearch.Full.RefinedChoresClosedCaches
import EnvyFreeResearch.Full.ChoresTerminalAggregate

/-! Literal affine donors remain in the closed package and full pool, with
root-local owner permutations and immutable original baselines. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
open Set MeasureTheory IntervalOracle OracleProtocol
open ChoreComposition Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (A : Finset (Fin n)) (p : Fin n)
    (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A)

def actualDonor (j : A) : ChoreComposition.Allocation (Fin n) RootId :=
  (donorProposal A p frames hpath gap out j).output

theorem actual_donation_mem (j : A) :
    (⟨packages (out.allocation.assigned j),donorProposal A p frames hpath gap out j⟩ :
      Donation (Fin n) RootId) ∈ donations A p frames hpath packages gap out := by
  unfold donations Chores.ComponentAffine.tasks
  apply List.mem_map.mpr
  refine ⟨j,Finset.mem_toList.mpr j.property,?_⟩
  simp only [Function.comp_apply,donorRoot,donorProposal,dite_eq_left j.property]

theorem actual_donor_member (hmany : Fintype.card A < Fintype.card Root) (j : A) :
    actualDonor A p frames hpath gap out j ∈
      (outputPackage A p frames hpath packages gap out hmany).allocations := by
  unfold outputPackage mergeClosed Package.allocations
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨packages (out.allocation.assigned j),donorProposal A p frames hpath gap out j⟩,
    actual_donation_mem A p frames hpath packages gap out j,?_⟩
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem actual_donor_full_pool_member (frozen : List (Package (Fin n) RootId))
    (hmany : Fintype.card A < Fintype.card Root) (j : A) :
    actualDonor A p frames hpath gap out j ∈
      (frozen++[outputPackage A p frames hpath packages gap out hmany]).flatMap Package.allocations := by
  apply List.mem_flatMap.mpr
  exact ⟨_,List.mem_append_right _ (List.mem_singleton.mpr rfl),
    actual_donor_member A p frames hpath packages gap out hmany j⟩

theorem actual_donor_owner (j : A) : (actualDonor A p frames hpath gap out j).owner p = j := by
  simp only [actualDonor,donorProposal,affineProposal,Proposal.output,ite_true,owners,dite_eq_left j.property]
  exact RefinedChoresDirectedMatching.donor_recipient _ _ _ _

theorem actual_donor_baseline (j : A) (i : Fin n) :
    (actualDonor A p frames hpath gap out j).baseline i = (frames (out.allocation.assigned j)).baseline i := by
  simp only [actualDonor,donorProposal,affineProposal,Proposal.output,ite_true]

theorem actual_donor_root (j : A) :
    (actualDonor A p frames hpath gap out j).root = (frames (out.allocation.assigned j)).root := by
  simp only [actualDonor,donorProposal,affineProposal,Proposal.output,ite_true]

end EnvyFreeResearch.Full.RefinedChoresTerminalAggregate
