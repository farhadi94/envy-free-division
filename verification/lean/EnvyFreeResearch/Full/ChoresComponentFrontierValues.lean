import EnvyFreeResearch.Full.ChoresComponentFrames
import EnvyFreeResearch.Full.ChoresPackageProposal

/-! The frontier threshold is the original suffix cost minus the original gap.
Containment of recorded equalizers gives the old-allowed reserve inequalities. -/

namespace EnvyFreeResearch.Full.Chores.ComponentFrames
open Set MeasureTheory ChoreComposition

variable {Agent RootId : Type*} [DecidableEq Agent]

theorem original_frontier_value (cost : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] (frame : Frame Agent RootId)
    (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (block : Set ℝ) (gap : Agent → ℝ) (p q : Agent)
    (hsub : equalizer p q ⊆ parent p) (hmeas : MeasurableSet (equalizer p q))
    (hblock : block = parent p \ equalizer p q)
    (hequalizer : ∀ i, frame.equalizerCost i p q = (cost i).real (equalizer p q))
    (hgap : ∀ i, gap i = (cost i).real (parent p) - frame.baseline i) (i : Agent) :
    frame.gap i q p = (cost i).real block - gap i := by
  rw [Frame.gap, hequalizer, hblock, measureReal_sdiff hsub hmeas, hgap]
  ring

theorem contained_frontier_gap (cost : Agent → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] (frame : Frame Agent RootId)
    (equalizer : Agent → Agent → Set ℝ) (p q j i : Agent)
    (hcontain : equalizer p q ⊆ equalizer p j)
    (hequalizer : ∀ k, frame.equalizerCost i p k = (cost i).real (equalizer p k)) :
    frame.gap i j p ≤ frame.gap i q p := by
  have h := measureReal_mono (μ := cost i) hcontain
  simp only [Frame.gap, hequalizer]
  linarith

end EnvyFreeResearch.Full.Chores.ComponentFrames
