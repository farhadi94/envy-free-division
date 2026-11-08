import EnvyFreeResearch.Full.ChoresTerminalExtractionMarked
import EnvyFreeResearch.Full.ChoresTerminalExtractionPatched
import EnvyFreeResearch.Full.ChoresTerminalAggregateResidue
import EnvyFreeResearch.Full.ChoresTerminalResidue

/-! The actual atomic remainder has a recorded cache and the full physical
small-residue bound after extracting every complete assigned suffix once. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open ComponentRecording ComponentPayments ComponentExtraction
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (A : Finset (Fin n))
  (out : ComponentClosed.Result (Root := Fin data.size) A)
  (oldPrivate : RootId → Fin n → List (Parent n))

def remainingPrivate := Outer.removePrivate (Outer.terminalPrivateCache data original A out oldPrivate)
  (extractedSlots data A out)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (R : Set ℝ) (H : ℝ) (hH : 0 < H)
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost (fun i => (cost i).real R) H)
  (hparts : PartsCorrect cost (domains (blocks data original (fun i => (cost i).real R) H)
    data.pending.partition.representative) Subtype.val out)
  (hold : Outer.PrivateCorrect (measureProfile cost) (fun root p => (original root).piece p)
    data.cache oldPrivate)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(original root).piece p)

include hH hsound good hparts hold hG

theorem actual_remaining_slot_small (root : RootId) (p i : Fin n) :
    (cost i).real (material (remainingPrivate data original A out oldPrivate root p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  let priv := Outer.terminalPrivateCache data original A out oldPrivate
  have hp := residue_private_correct data original (fun i => (cost i).real R) H A out oldPrivate
    cost c hsound good hparts hold G hG
  have hsub : ∀ root p, material (priv root p) ⊆ G.piece root p := by
    intro root p
    rw [(hp root p).2.2]
    exact sdiff_subset
  have hd := Outer.marked_remainder_disjoint G priv (extractedSlots data A out) hsub
  have heq := marked_private_eq_extracted data original A out oldPrivate
    (Outer.active_roots_injective data original cost _ H good)
  rw [heq] at hd
  have hs : material (remainingPrivate data original A out oldPrivate root p) ⊆
      ((original root).piece p \ material (updatedCache data original (fun i => (cost i).real R) H A out root p)) \
        extracted out := by
    intro x hx
    constructor
    · have hx' := Outer.remove_private_subset priv (extractedSlots data A out) root p hx
      rw [(hp root p).2.2,hG] at hx'
      exact hx'
    · intro hxX
      exact disjoint_left.mp hd hxX (mem_iUnion.mpr ⟨root,mem_iUnion.mpr ⟨p,hx⟩⟩)
  exact (measureReal_mono (μ := cost i) hs).trans
    (terminal_patched_complement_outside_extracted_small data original (fun i => (cost i).real R)
      H A out cost c hsound good (fun _ => measureReal_nonneg) hH hparts root p i)

theorem actual_atomic_residue_bounds (J : ℕ) (hcard : Fintype.card RootId ≤ J) (i : Fin n) :
    (cost i).real R ≤ (cost i).real (R ∪ Outer.privateUnion (remainingPrivate data original A out oldPrivate)) ∧
    (cost i).real (R ∪ Outer.privateUnion (remainingPrivate data original A out oldPrivate)) ≤
      (1+(J : ℝ)*(n : ℝ)^2/H)*(cost i).real R :=
  full_residue_bounds (cost i) R (remainingPrivate data original A out oldPrivate) J H hH hcard
    (fun root p => actual_remaining_slot_small data original A out oldPrivate cost R H hH c hsound
      good hparts hold G hG root p i)

end EnvyFreeResearch.Full.Chores.Terminal
