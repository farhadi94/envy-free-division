import EnvyFreeResearch.Full.UpperGlobalPhysicalFinishActual

/-! Proof-only transport witness for the actual accepted final Repair. The
local receiver is tied to the original-population WholeAddition permutation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
open UpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution UpperZeroRows
open UpperCircularStage UpperRepairPreparationChecks GlobalCompletion UpperGlobalPhysicalRepair
variable {n : ℕ}

structure Witness (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : Pending n) (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card) where
  receiver : Equiv.Perm (Fin p.anchor.active.card)
  addition : Fin p.anchor.active.card → State n
  label : ∀ j, domain (result.1 (receiver j)).cells =
    domain (localEndowments p j).cells ∪ domain (addition j).cells
  subset_buffer : ∀ j, domain (addition j).cells ⊆ domain p.buffer.cells
  balance : ∀ i, (∑ j, (μ i).real (domain (addition j).cells)) +
    (μ i).real (domain result.2.1.cells) = (μ i).real (domain p.buffer.cells)
  quarter : ∀ i, (∑ j, (μ (enumerate p.anchor.active i)).real (domain (addition j).cells)) <
    (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells) / 4
  whole : WholeAddition (p.anchor.table μ).value ((finish p result).table μ).value
    (p.anchor.table μ).active (p.anchor.table μ).residue ((finish p result).table μ).residue
  receiver_eq : whole.permutation = extendPermutation p.anchor.active receiver

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) (hp : p.Physical μ whole)

include hp in
 theorem success_whole_witness (chores : Bool)
    (result : UpperRepairProgram.PhysicalResult n p.anchor.active.card)
    (facts : UpperRepairProgram.SuccessFacts μ chores (enumerate p.anchor.active)
      p.buffer (localEndowments p) result)
    (f : Equiv.Perm (Fin p.anchor.active.card)) (localAdded : Fin p.anchor.active.card → State n)
    (hl : ∀ j, domain (result.1 (f j)).cells = domain (localEndowments p j).cells ∪ domain (localAdded j).cells)
    (hsub : ∀ j, domain (localAdded j).cells ⊆ domain p.buffer.cells) :
    ∃ ht : WholeAddition (p.anchor.table μ).value ((finish p result).table μ).value
      (p.anchor.table μ).active (p.anchor.table μ).residue ((finish p result).table μ).residue,
      ht.permutation = extendPermutation p.anchor.active f := by
  have hpair := additions_pairwise (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f hl facts.allocation_disjoint
  have hsep := additions_separate (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f
    (domain result.2.1.cells) hl facts.residue_disjoint
  have hcover := additions_partition (fun j => domain (localEndowments p j).cells)
    (fun j => domain (localAdded j).cells) (fun j => domain (result.1 j).cells) f
    (domain p.buffer.cells) (domain result.2.1.cells) hl facts.material_preserved
    (localEndowments_separate μ whole p hp) hsub facts.residue_subset
  exact ⟨receivedWholeAddition μ whole p.anchor hp.anchor (output p result.1)
    (added p localAdded result.2.1.history) result.2.1 (extendPermutation p.anchor.active f)
    (output_whole_label μ whole p hp result.1 localAdded result.2.1.history f hl)
    (added_pairwise μ whole p hp localAdded result.2.1 hsub hpair)
    (added_separate μ whole p hp localAdded result.2.1 facts.residue_subset hsep)
    (added_cover μ whole p hp localAdded result.2.1 hcover)
    (extendPermutation_fixed p.anchor.active f)
    (added_frozen μ whole p hp localAdded result.2.1.history),rfl⟩

variable [Nonempty (Fin p.anchor.active.card)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
  (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
  (hnear : Near chores μ (enumerate p.anchor.active) p.buffer (localEndowments p) (UpperRepair.nearError n))
  (tape : UpperRepair.Tape n p.anchor.active.card)
  (hsuccess : (UpperRepair.execute policy hk chores (enumerate p.anchor.active)
    p.buffer (localEndowments p) tape).2.2 = false)
include hp hpolicy hpositive hnear hsuccess in
 theorem actual_finish_witness : Nonempty (Witness μ p (UpperRepair.execute policy hk chores
    (enumerate p.anchor.active) p.buffer (localEndowments p) tape)) := by
  have hold := localEndowments_wf μ whole p hp
  have hpair := localEndowments_pair μ whole p hp
  have hsep := localEndowments_separate μ whole p hp
  have hhist := localEndowments_history p
  have facts := UpperRepair.success_facts μ policy hpolicy hk chores (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p) hold hnear
    hpair hsep hhist tape hsuccess
  obtain ⟨f,localAdded,hl,hsub,hbalance,hquarter⟩ :=
    UpperGlobalPhysicalRepair.actual_transport μ policy hpolicy hk chores (enumerate p.anchor.active)
      (enumerate_injective _) p.buffer hp.buffer_wf hpositive (localEndowments p) hold hnear
      hpair hsep hhist tape hsuccess
  obtain ⟨ht,hperm⟩ := success_whole_witness μ whole p hp chores _ facts f localAdded hl hsub
  exact ⟨⟨f,localAdded,hl,hsub,hbalance,hquarter,ht,hperm⟩⟩

end EnvyFreeResearch.Full.UpperGlobalPhysicalFinish
