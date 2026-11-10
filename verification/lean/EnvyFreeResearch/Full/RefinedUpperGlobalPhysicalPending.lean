import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMachine

/-! Literal material invariant between Snapshot and the final Repair. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperEndpointCache
variable {n : ℕ}

structure Pending.Physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n) : Prop where
  anchor : p.anchor.Physical μ whole
  snapshot_wf : ∀ j, WellFormed μ (p.snapshot j)
  shrunk_wf : ∀ j, WellFormed μ (p.shrunk j)
  buffer_wf : WellFormed μ p.buffer
  snapshot_pair : Pairwise (fun i j => Disjoint (domain (p.snapshot i).cells) (domain (p.snapshot j).cells))
  shrunk_pair : Pairwise (fun i j => Disjoint (domain (p.shrunk i).cells) (domain (p.shrunk j).cells))
  cross : ∀ i j, Disjoint (domain (p.shrunk i).cells) (domain (p.snapshot j).cells)
  snapshot_sep : ∀ j, Disjoint (domain (p.snapshot j).cells) (domain p.buffer.cells)
  shrunk_sep : ∀ j, Disjoint (domain (p.shrunk j).cells) (domain p.buffer.cells)
  cover : (⋃ j, domain (p.shrunk j).cells) ∪ (⋃ j, domain (p.snapshot j).cells) ∪
    domain p.buffer.cells = domain p.anchor.residue.cells
  old_history : ∀ j, (p.anchor.bundles j).history ⊆ p.buffer.history
  snapshot_history : ∀ j, (p.snapshot j).history ⊆ p.buffer.history
  shrunk_history : ∀ j, (p.shrunk j).history ⊆ p.buffer.history
  snapshot_frozen : ∀ j ∉ p.anchor.active, domain (p.snapshot j).cells = ∅
  shrunk_frozen : ∀ j ∉ p.anchor.active, domain (p.shrunk j).cells = ∅
  permutation_frozen : ∀ j ∉ p.anchor.active, p.permutation j = j

def Pending.additions (p : Pending n) (j : Fin n) : State n :=
  join (p.shrunk j) (p.snapshot (p.permutation j)) p.buffer.history

def Pending.provisional (p : Pending n) : Anchor n :=
  commit p.anchor p.additions p.buffer (Equiv.refl _)

theorem provisional_bundles (p : Pending n) : p.provisional.bundles = p.endowments := rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole)
include hp

theorem pending_additions_wf (j : Fin n) : WellFormed μ (p.additions j) :=
  join_wellFormed μ _ _ _ (hp.shrunk_wf j) (hp.snapshot_wf _)
    (hp.cross j _) hp.buffer_wf.2.2.1 (hp.shrunk_history j) (hp.snapshot_history _)

theorem pending_additions_pair : Pairwise (fun i j =>
    Disjoint (domain (p.additions i).cells) (domain (p.additions j).cells)) := by
  intro i j hij
  simp only [Pending.additions,join_domain,disjoint_union_left,disjoint_union_right]
  exact ⟨⟨hp.shrunk_pair hij,(hp.cross j _).symm⟩,
    ⟨hp.cross i _,hp.snapshot_pair (p.permutation.injective.ne hij)⟩⟩

theorem pending_additions_separate (j : Fin n) :
    Disjoint (domain (p.additions j).cells) (domain p.buffer.cells) := by
  simp only [Pending.additions,join_domain,disjoint_union_left]
  exact ⟨hp.shrunk_sep j,hp.snapshot_sep _⟩

theorem pending_additions_cover :
    (⋃ j, domain (p.additions j).cells) ∪ domain p.buffer.cells = domain p.anchor.residue.cells := by
  simp only [Pending.additions,join_domain,iUnion_union_distrib]
  rw [p.permutation.surjective.iUnion_comp (fun j => domain (p.snapshot j).cells)]
  exact hp.cover

theorem pending_additions_frozen (j : Fin n) (hj : j ∉ p.anchor.active) :
    domain (p.additions j).cells = ∅ := by
  simp only [Pending.additions,join_domain,hp.permutation_frozen j hj,
    hp.shrunk_frozen j hj,hp.snapshot_frozen j hj,union_empty]

theorem pending_provisional_physical : p.provisional.Physical μ whole := by
  exact commit_physical μ whole p.anchor hp.anchor p.additions p.buffer (Equiv.refl _)
    (pending_additions_wf μ whole p hp) hp.buffer_wf
    (pending_additions_pair μ whole p hp) (pending_additions_separate μ whole p hp)
    (pending_additions_cover μ whole p hp) hp.old_history (fun _ _ hx => hx)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
