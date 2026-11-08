import EnvyFreeResearch.Full.ChoresOuterPrivateBatch
import EnvyFreeResearch.Full.ChoresOuterPrivateClosed
import EnvyFreeResearch.Full.ChoresTerminalCache

/-! Actual terminal affine updates retain exact caches for all complements. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ComponentRecording ComponentPayments
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)

def terminalPrivateCache (oldPrivate : RootId → Fin n → List (Parent n)) :
    RootId → Fin n → List (Parent n) :=
  ComponentPhysical.patchCache data.frames oldPrivate
    (closedPrivateCache data.pending data.visited A data.frames
      (originalGaps data original) out (equalizerSuffixCache data original))

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hparts : PartsCorrect cost (domains (Terminal.blocks data original r H)
    data.pending.partition.representative) Subtype.val out)
include hsound good hparts

theorem terminal_private_correct (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache oldPrivate) :
    PrivateCorrect (measureProfile cost) (fun root => (original root).piece)
      (Terminal.updatedCache data original r H A out)
      (terminalPrivateCache data original A out oldPrivate) := by
  apply private_patch data.frames (measureProfile cost) (fun root => (original root).piece)
    data.cache oldPrivate _ _ hold
  intro s p
  rw [good.source s]
  apply closed_private_correct data.pending data.visited A data.frames
    (originalGaps data original) out (equalizerCache data original)
    (equalizerSuffixCache data original) (Terminal.fronts data original r H)
    cost (fun s => (original (data.source s)).piece) (Terminal.blocks data original r H)
    (Terminal.parent_unit data original cost c hsound)
    (Terminal.fronts_valid data original r H cost c hsound)
    (Terminal.equalizers_valid data original cost c hsound)
    (Terminal.fronts_subset data original r H cost c hsound)
    (Terminal.blocks_complement data original r H cost c hsound) hparts
  intro t q j
  obtain ⟨U,hs⟩ := hsound (data.source t)
  exact private_equalizer cost _ c U hs q j
end EnvyFreeResearch.Full.Chores.Outer
