import EnvyFreeResearch.Full.RefinedChoresTerminalCohort

/-! The selected terminal class supplies a proper nonempty recursive
 population; this is derived from physical scans and the omitted pivot. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (homitted : ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible
      (original (data.source s)) H r data.protectedLabel)
include hsound horiginal hsep hr hH hscale hr_eq homitted

theorem TerminalGroup.admissible :
    group.terminalClass.participants.Nonempty ∧ group.terminalClass.participants ≠ Finset.univ := by
  let s : group.Root := ⟨0,by simp [TerminalGroup.Root]⟩
  have h := TerminalGroup.common data normal original r H group cost xs index c hsound horiginal R
    hsep hr hH hscale hr_eq homitted s
  exact ⟨⟨group.label,h.1⟩,h.2.2.1⟩

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.admissible
