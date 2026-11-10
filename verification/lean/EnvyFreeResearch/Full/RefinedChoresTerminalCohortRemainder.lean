import EnvyFreeResearch.Full.RefinedChoresTerminalCohortExtraction
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortComplement
import EnvyFreeResearch.Full.ChoresTerminalAggregateResidue

/-! Uniform bounds on the actual remainder after all assigned suffix slots
 are removed, including every unselected and frozen original root. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n))

def TerminalGroup.remainingPrivate := Outer.removePrivate
  (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
  (TerminalGroup.marked data normal original r H group out)

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
    (hparts : PartsCorrect cost
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (hold : Outer.PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
include hsound good hparts hold hG

theorem TerminalGroup.remaining_slot_small (root : RootId) (a i : Fin n) :
    (cost i).real (material (TerminalGroup.remainingPrivate data normal original r H group hr0 hH0 out oldPrivate root a)) ≤
      (n : ℝ)*r i/H := by
  let priv := TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate
  let marked := TerminalGroup.marked data normal original r H group out
  have hs := TerminalGroup.private_subset data normal original r H group hr0 hH0 out oldPrivate
    cost c hsound good hparts hold G hG
  have hd := Outer.marked_remainder_disjoint G priv marked hs
  rw [TerminalGroup.marked_exact data normal original r H group hr0 hH0 out oldPrivate cost good] at hd
  have hsub : material (Outer.removePrivate priv marked root a) ⊆ material (priv root a) \ extracted out := by
    intro x hx
    refine ⟨Outer.remove_private_subset priv marked root a hx,?_⟩
    intro hX
    exact disjoint_left.mp hd hX (mem_iUnion.mpr ⟨root,mem_iUnion.mpr ⟨a,hx⟩⟩)
  exact (measureReal_mono (μ := cost i) hsub).trans
    (TerminalGroup.pool_private_outside_small data normal original r H group hr0 hH0 out cost c hsound
      good hparts oldPrivate hold (extracted out) (fun j x hx => mem_iUnion.mpr ⟨j,hx⟩) root a i)

theorem TerminalGroup.remaining_bounds (R : Set ℝ) (hr_eq : r = fun i => (cost i).real R)
    (J : ℕ) (hcard : Fintype.card RootId ≤ J) (i : Fin n) :
    (cost i).real R ≤ (cost i).real (R ∪ Outer.privateUnion
      (TerminalGroup.remainingPrivate data normal original r H group hr0 hH0 out oldPrivate)) ∧
    (cost i).real (R ∪ Outer.privateUnion
      (TerminalGroup.remainingPrivate data normal original r H group hr0 hH0 out oldPrivate)) ≤
      (1+(J : ℝ)*(n : ℝ)^2/H)*(cost i).real R := by
  apply Terminal.full_residue_bounds (cost i) R _ J H hH0 hcard
  intro root a
  simpa only [hr_eq] using TerminalGroup.remaining_slot_small data normal original r H group hr0 hH0 out
    oldPrivate cost c hsound good hparts hold G hG root a i

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.remaining_bounds
