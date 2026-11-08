import EnvyFreeResearch.Full.ChoresTerminalAggregatePrivate
import EnvyFreeResearch.Full.ChoresTerminalAggregateResidue
import EnvyFreeResearch.Full.ChoresTerminalResidue

/-! The entire actual exhausted residue, including the private remnants of
old frozen ancestors, is bounded by the original untouched residue. -/
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


variable (hsmall : ∀ j : A, ∀ s i,
  (cost i).real (blocks data original (fun k => (cost k).real R) H s
    (data.pending.partition.representative j)) ≤ (n : ℝ)*(cost i).real R/H)

include hH hsound good hparts hold hG hsmall

theorem actual_exhausted_slot_small (root : RootId) (p i : Fin n) :
    (cost i).real (material (Outer.terminalPrivateCache data original A out oldPrivate root p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  have hp := residue_private_correct data original (fun i => (cost i).real R) H A out oldPrivate
    cost c hsound good hparts hold G hG
  rw [(hp root p).2.2,hG]
  exact exhausted_patched_complement_small data original (fun i => (cost i).real R) H A out cost c
    hsound good (fun _ => measureReal_nonneg) hH hparts hsmall root p i

theorem actual_exhausted_residue_bounds (J : ℕ) (hcard : Fintype.card RootId ≤ J) (i : Fin n) :
    (cost i).real R ≤ (cost i).real
      (R ∪ Outer.privateUnion (Outer.terminalPrivateCache data original A out oldPrivate)) ∧
    (cost i).real (R ∪ Outer.privateUnion (Outer.terminalPrivateCache data original A out oldPrivate)) ≤
      (1+(J : ℝ)*(n : ℝ)^2/H)*(cost i).real R :=
  full_residue_bounds (cost i) R (Outer.terminalPrivateCache data original A out oldPrivate) J H hH hcard
    (fun root p => actual_exhausted_slot_small data original A out oldPrivate cost R H hH c hsound
      good hparts hold G hG hsmall root p i)

end EnvyFreeResearch.Full.Chores.Terminal
