import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPendingMass
import EnvyFreeResearch.Full.UpperRepairPreparationChecks

/-! Near-envy-freeness and the strong saved comparison are consequences of
the actual joined endowment identity, not assumptions about Repair's input. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (p : Pending n)
  (hWH : ∀ j, Disjoint (domain (p.anchor.bundles j).cells) (domain (p.shrunk j).cells))
  (hWX : ∀ j, Disjoint (domain (p.anchor.bundles j).cells)
    (domain (p.snapshot (p.permutation j)).cells))
  (hHX : ∀ j, Disjoint (domain (p.shrunk j).cells)
    (domain (p.snapshot (p.permutation j)).cells))
  (direction : Direction)
  (hW : ActiveEF direction (value μ p.anchor.bundles) p.anchor.active)
  (hH : ActiveEF direction (value μ p.shrunk) p.anchor.active)
  (tau : ℝ)
  (hown : ∀ i ∈ p.anchor.active, margin direction (value μ p.snapshot) i (p.permutation i) ≤
    tau * (μ i).real (domain p.buffer.cells))

include hWH hWX hHX hW hH hown in
theorem pending_near_margin
    (hX : ActiveEF direction (value μ p.snapshot) p.anchor.active)
    (hperm : ∀ j ∈ p.anchor.active, p.permutation j ∈ p.anchor.active)
    (i j : Fin n) (hi : i ∈ p.anchor.active) (hj : j ∈ p.anchor.active) :
    -(tau * (μ i).real (domain p.buffer.cells)) ≤ margin direction (value μ p.endowments) i j := by
  rw [pending_margin_identity μ p hWH hWX hHX]
  have hw := hW i hi j hj
  have hh := hH i hi j hj
  have hx := hX i hi (p.permutation j) (hperm j hj)
  have ho := hown i hi
  linarith

include hWH hWX hHX hW hH hown in
theorem pending_strong_margin
    (hb : p.witness ∈ p.anchor.active) (hh : p.target ∈ p.anchor.active)
    (hlarge : 2 * (μ p.witness).real (domain p.buffer.cells) ≤
      margin direction (value μ p.snapshot) p.witness (p.permutation p.target)) :
    (2-tau) * (μ p.witness).real (domain p.buffer.cells) ≤
      margin direction (value μ p.endowments) p.witness p.target := by
  rw [pending_margin_identity μ p hWH hWX hHX]
  have hw := hW p.witness hb p.target hh
  have hs := hH p.witness hb p.target hh
  have ho := hown p.witness hb
  nlinarith

theorem pending_repair_near {k : ℕ} [Nonempty (Fin k)]
    (chores : Bool) (active : Fin k → Fin n)
    (hactive : ∀ i, active i ∈ p.anchor.active)
    (hmargin : ∀ i ∈ p.anchor.active, ∀ j ∈ p.anchor.active,
      -(tau * (μ i).real (domain p.buffer.cells)) ≤
      margin (if chores then .chore else .cake) (value μ p.endowments) i j) :
    UpperRepairPreparationChecks.Near chores μ active p.buffer
      (fun j => p.endowments (active j)) tau := by
  intro i j
  have hm := hmargin (active i) (hactive i) (active j) (hactive j)
  cases chores <;> simp only [Bool.false_eq_true, ↓reduceIte,margin,value] at hm ⊢ <;> linarith

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
