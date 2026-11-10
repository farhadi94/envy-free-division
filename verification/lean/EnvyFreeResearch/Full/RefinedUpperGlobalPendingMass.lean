import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolMachine

/-! Literal physical mass identities for the recorded endowments passed to
the final Repair. Whole saved and shrunk bundles stay with their owners. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly
variable {n : ℕ}

theorem pending_endowment_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p : Pending n) (j : Fin n)
    (hWH : Disjoint (domain (p.anchor.bundles j).cells) (domain (p.shrunk j).cells))
    (hWX : Disjoint (domain (p.anchor.bundles j).cells)
      (domain (p.snapshot (p.permutation j)).cells))
    (hHX : Disjoint (domain (p.shrunk j).cells)
      (domain (p.snapshot (p.permutation j)).cells)) :
    μ.real (domain (p.endowments j).cells) = μ.real (domain (p.anchor.bundles j).cells) +
      μ.real (domain (p.shrunk j).cells) + μ.real (domain (p.snapshot (p.permutation j)).cells) := by
  rw [endowments_domain,measureReal_union (disjoint_union_left.mpr ⟨hWX,hHX⟩)
    (domain_measurable _),measureReal_union hWH (domain_measurable _)]

theorem pending_endowment_value (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : Pending n)
    (hWH : ∀ j, Disjoint (domain (p.anchor.bundles j).cells) (domain (p.shrunk j).cells))
    (hWX : ∀ j, Disjoint (domain (p.anchor.bundles j).cells)
      (domain (p.snapshot (p.permutation j)).cells))
    (hHX : ∀ j, Disjoint (domain (p.shrunk j).cells)
      (domain (p.snapshot (p.permutation j)).cells)) (i j : Fin n) :
    value μ p.endowments i j = value μ p.anchor.bundles i j + value μ p.shrunk i j +
      value μ p.snapshot i (p.permutation j) :=
  pending_endowment_mass (μ i) p j (hWH j) (hWX j) (hHX j)

theorem pending_margin_identity (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : Pending n)
    (hWH : ∀ j, Disjoint (domain (p.anchor.bundles j).cells) (domain (p.shrunk j).cells))
    (hWX : ∀ j, Disjoint (domain (p.anchor.bundles j).cells)
      (domain (p.snapshot (p.permutation j)).cells))
    (hHX : ∀ j, Disjoint (domain (p.shrunk j).cells)
      (domain (p.snapshot (p.permutation j)).cells))
    (direction : GlobalCompletion.Direction) (i j : Fin n) :
    GlobalCompletion.margin direction (value μ p.endowments) i j =
      GlobalCompletion.margin direction (value μ p.anchor.bundles) i j +
      GlobalCompletion.margin direction (value μ p.shrunk) i j +
      GlobalCompletion.margin direction (value μ p.snapshot) i (p.permutation j) -
      GlobalCompletion.margin direction (value μ p.snapshot) i (p.permutation i) := by
  cases direction <;> simp only [GlobalCompletion.margin,
    pending_endowment_value μ p hWH hWX hHX] <;> ring

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
