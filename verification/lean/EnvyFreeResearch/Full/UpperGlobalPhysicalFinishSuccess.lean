import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishPartition
import EnvyFreeResearch.Full.UpperRepairSuccess

/-! Local successful Repair facts imply a committed original-population
allocation through literal physical transport and the old frozen guards. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
open UpperGlobalPhysicalRepair GlobalCompletion
variable {n : ℕ}

def localEndowments (p : Pending n) : Fin p.anchor.active.card → State n :=
  fun i => p.endowments (enumerate p.anchor.active i)

def finish (p : Pending n) (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) : Anchor n :=
  received p.anchor (output p result.1) result.2.1

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)
include hp

theorem localEndowments_wf : ∀ i, WellFormed μ (localEndowments p i) := by
  intro i
  exact (pending_provisional_physical μ whole p hp).bundles_wellFormed _

theorem localEndowments_pair : Pairwise (fun i j =>
    Disjoint (domain (localEndowments p i).cells) (domain (localEndowments p j).cells)) := by
  intro i j hij
  exact (pending_provisional_physical μ whole p hp).pairwise
    (fun he => hij (enumerate_injective _ he))

theorem localEndowments_separate : ∀ i,
    Disjoint (domain (localEndowments p i).cells) (domain p.buffer.cells) := by
  intro i
  exact (pending_provisional_physical μ whole p hp).separate _

omit hp
 theorem localEndowments_history : ∀ i, (localEndowments p i).history ⊆ p.buffer.history :=
  fun _ _ hx => hx

 theorem success_activeEF (chores : Bool) (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : UpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result) :
    ActiveEF (if chores then .chore else .cake) (value μ (output p result.1)) p.anchor.active := by
  intro i hi j hj
  obtain ⟨a,rfl⟩ := enumerate_preimage _ i hi
  obtain ⟨b,rfl⟩ := enumerate_preimage _ j hj
  cases chores <;> simpa only [Bool.false_eq_true,if_false,if_true,margin,value,output_active,sub_nonneg]
    using facts.envyFree a b

include hp
 theorem success_finish (chores : Bool)
    (hvalid : Valid (if chores then .chore else .cake) (p.anchor.table μ))
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : UpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result)
    (f : Equiv.Perm (Fin p.anchor.active.card))
    (localAdded : Fin p.anchor.active.card → State n)
    (hl : ∀ j, domain (result.1 (f j)).cells = domain (localEndowments p j).cells ∪ domain (localAdded j).cells)
    (hsub : ∀ j, domain (localAdded j).cells ⊆ domain p.buffer.cells) :
    (finish p result).Committed μ (if chores then .chore else .cake) whole ∧
    Nonempty (WholeAddition (p.anchor.table μ).value ((finish p result).table μ).value
      (p.anchor.table μ).active (p.anchor.table μ).residue ((finish p result).table μ).residue) := by
  have hpair := additions_pairwise (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f hl facts.allocation_disjoint
  have hsep := additions_separate (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f
    (domain result.2.1.cells) hl facts.residue_disjoint
  have hcover := additions_partition (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f
    (domain p.buffer.cells) (domain result.2.1.cells) hl facts.material_preserved
    (localEndowments_separate μ whole p hp) hsub facts.residue_subset
  have hwhole := output_whole_label μ whole p hp result.1 localAdded result.2.1.history f hl
  have hpair' := added_pairwise μ whole p hp localAdded result.2.1 hsub hpair
  have hsep' := added_separate μ whole p hp localAdded result.2.1 facts.residue_subset hsep
  have hcover' := added_cover μ whole p hp localAdded result.2.1 hcover
  have hfix := extendPermutation_fixed p.anchor.active f
  have hfrozen := added_frozen μ whole p hp localAdded result.2.1.history
  refine ⟨?_,⟨receivedWholeAddition μ whole p.anchor hp.anchor (output p result.1)
    (added p localAdded result.2.1.history) result.2.1 (extendPermutation p.anchor.active f)
    hwhole hpair' hsep' hcover' hfix hfrozen⟩⟩
  exact received_committed μ whole p.anchor hp.anchor (output p result.1)
    (added p localAdded result.2.1.history) result.2.1 (extendPermutation p.anchor.active f)
    hwhole hpair' hsep' hcover' hfix hfrozen _ hvalid
    (output_wellFormed μ whole p hp result.1 facts.allocation_wellFormed)
    facts.residue_wellFormed (success_activeEF μ p chores result facts)

end EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
