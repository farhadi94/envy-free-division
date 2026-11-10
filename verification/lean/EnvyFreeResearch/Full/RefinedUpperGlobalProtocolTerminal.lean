import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalInvariant
import EnvyFreeResearch.Full.UpperZeroRows

/-! Complete active allocations are committed under their original owners.
This applies to the concrete zero-, one-, and two-agent base protocols. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperEndpointCache
variable {n : ℕ}

def terminal (a : Anchor n) (addition : Fin n → State n) (history : UpperCircularStage.History n) : Anchor n :=
  commit a addition (empty history) (Equiv.refl _)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (direction : GlobalCompletion.Direction)
  (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ direction whole)
  (addition : Fin n → State n) (history : UpperCircularStage.History n)
  (htruth : Truthful μ history) (hadd : ∀ j, WellFormed μ (addition j))
  (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
  (hcover : (⋃ j, domain (addition j).cells) = domain a.residue.cells)
  (hfrozen : ∀ j ∉ a.active, domain (addition j).cells = ∅)
  (holdhist : ∀ j, (a.bundles j).history ⊆ history)
  (haddhist : ∀ j, (addition j).history ⊆ history)
  (hef : GlobalCompletion.ActiveEF direction (value μ addition) a.active)
include ha htruth hadd hpair hcover hfrozen holdhist haddhist hef

theorem terminal_committed : (terminal a addition history).Committed μ direction whole := by
  have hdis (j : Fin n) : Disjoint (domain (a.bundles j).cells) (domain (addition j).cells) := by
    apply (ha.1.separate j).mono_right
    rw [← hcover]
    exact subset_iUnion (fun j => domain (addition j).cells) j
  have hv : value μ (terminal a addition history).bundles =
      fun i j => value μ a.bundles i j + value μ addition i j := by
    funext i j
    exact transport_value (μ i) a.bundles addition (Equiv.refl _) history hdis j
  apply commit_committed μ direction whole a ha addition (empty history) (Equiv.refl _)
    (fun _ _ => rfl) hfrozen hadd (empty_wellFormed μ history htruth) hpair
    (fun j => by simp [empty,domain]) (by simpa [empty,domain] using hcover) holdhist haddhist
  change GlobalCompletion.ActiveEF direction (value μ (terminal a addition history).bundles) a.active
  rw [hv]
  intro i hi j hj
  rw [GlobalCompletion.margin_add]
  exact add_nonneg (ha.2.2.2.1 i j) (hef i hi j hj)

theorem terminal_complete :
    (⋃ j, domain ((terminal a addition history).bundles j).cells) = whole := by
  have h := (terminal_committed μ direction whole a ha addition history htruth hadd hpair hcover
    hfrozen holdhist haddhist hef).1.cover
  simpa only [terminal,commit,empty,domain,union_empty] using h

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
