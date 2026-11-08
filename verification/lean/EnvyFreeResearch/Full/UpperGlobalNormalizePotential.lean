import EnvyFreeResearch.Full.UpperGlobalNormalizeSnapshot
import EnvyFreeResearch.Full.UpperGlobalNormalizeCorrectness
import EnvyFreeResearch.Full.UpperGlobalRunBudgetTerminal

/-! The actual normalization dispatcher never decreases cached domination
potential: nonterminal freezing preserves all values, and completion saturates it. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open UpperGlobalPhysical UpperCircularStage GlobalCompletion UpperGlobalRunBudget
variable {n : ℕ}

theorem Saved.cachedPotential {a b : Anchor n} (h : Saved a b) (direction : Direction) :
    b.cachedPotential direction = a.cachedPotential direction := by
  have hv : b.cachedValue = a.cachedValue := by
    funext i j
    unfold Anchor.cachedValue
    rw [h.1]
  simp only [Anchor.cachedPotential,hv,Anchor.cachedResidue,h.2.1]

theorem execute_potential (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (policy : Policy n)
    (hp : Admissible (Chores.measureProfile μ) policy) (fallback : Fin n)
    (chores : Bool) (whole : Set ℝ) (a : Anchor n)
    (ha : a.Committed μ (direction chores) whole) (hh : a.HistoryCompatible) (hn : a.active.Nonempty) :
    a.cachedPotential (direction chores) ≤
      (execute policy fallback chores a).anchor.cachedPotential (direction chores) := by
  have hv := execute_valid μ policy hp fallback chores whole a ha hh hn
  cases he : execute policy fallback chores a with
  | normalize b => rw [he] at hv; exact hv.elim
  | firstShrink p G => rw [he] at hv; exact hv.elim
  | secondShrink p => rw [he] at hv; exact hv.elim
  | finalRepair p => rw [he] at hv; exact hv.elim
  | snapshot b =>
    have hs := execute_snapshot_saved policy fallback chores a b he
    change a.cachedPotential _ ≤ b.cachedPotential _
    rw [hs.cachedPotential]
  | done b =>
    rw [he] at hv
    change a.cachedPotential _ ≤ b.cachedPotential _
    rw [show b.cachedPotential (direction chores)=n*(n-1) from valid_done_saturated μ whole chores b hv]
    exact cached_potential_le a _

end EnvyFreeResearch.Full.UpperGlobalNormalize
