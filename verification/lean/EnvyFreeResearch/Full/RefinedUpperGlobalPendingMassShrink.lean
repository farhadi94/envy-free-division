import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolShrink
import EnvyFreeResearch.Full.UpperPopulationExtensionFacts

/-! Literal additive margins when an accepted Shrink allocation is accumulated
under the original owners. All new material comes from the pending buffer. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
  GlobalCompletion
variable {n : ℕ}

theorem pending_addShrink_value (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : Pending n) (pieces : Fin n → State n) (residue : State n)
    (hsep : ∀ j, Disjoint (domain (p.shrunk j).cells) (domain p.buffer.cells))
    (hcover : (⋃ j, domain (pieces j).cells) ∪ domain residue.cells = domain p.buffer.cells)
    (i j : Fin n) :
    value μ (p.addShrink pieces residue).shrunk i j =
      value μ p.shrunk i j + value μ pieces i j := by
  have hs : domain (pieces j).cells ⊆ domain p.buffer.cells := by
    rw [← hcover]
    exact (subset_iUnion (fun j => domain (pieces j).cells) j).trans subset_union_left
  exact join_mass (μ i) _ _ _ ((hsep j).mono_right hs)

theorem pending_addShrink_activeEF (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : Pending n) (pieces : Fin n → State n) (residue : State n)
    (hsep : ∀ j, Disjoint (domain (p.shrunk j).cells) (domain p.buffer.cells))
    (hcover : (⋃ j, domain (pieces j).cells) ∪ domain residue.cells = domain p.buffer.cells)
    (direction : Direction)
    (hprior : ActiveEF direction (value μ p.shrunk) p.anchor.active)
    (hnew : ActiveEF direction (value μ pieces) p.anchor.active) :
    ActiveEF direction (value μ (p.addShrink pieces residue).shrunk) p.anchor.active := by
  intro i hi j hj
  have hw := hprior i hi j hj
  have hn := hnew i hi j hj
  have he : value μ (p.addShrink pieces residue).shrunk =
      fun a b => value μ p.shrunk a b + value μ pieces a b := by
    funext a b
    exact pending_addShrink_value μ p pieces residue hsep hcover a b
  rw [he,margin_add]
  exact add_nonneg hw hn

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
