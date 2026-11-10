import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalCommit

/-! All-observer guards and domination counts for the actual physical
whole-label commit. Zero rows are covered by saturation, not by an invalid
claim that every old proper target has a proper image. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (direction : GlobalCompletion.Direction)
  (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ direction whole)
  (addition : Fin n → State n) (remaining : State n) (f : Equiv.Perm (Fin n))
  (hfix : ∀ j ∉ a.active, f j = j)
  (hfrozen : ∀ j ∉ a.active, domain (addition j).cells = ∅)
  (hadd : ∀ j, WellFormed μ (addition j)) (hr : WellFormed μ remaining)
  (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
  (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
  (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain a.residue.cells)
  (holdhist : ∀ j, (a.bundles j).history ⊆ remaining.history)
  (haddhist : ∀ j, (addition j).history ⊆ remaining.history)
  (hactive : GlobalCompletion.ActiveEF direction (value μ (commit a addition remaining f).bundles) a.active)

include ha hpair hsep hcover hfix hfrozen in
def commitWholeAddition : GlobalCompletion.WholeAddition (a.table μ).value
    ((commit a addition remaining f).table μ).value (a.table μ).active
    (a.table μ).residue ((commit a addition remaining f).table μ).residue := by
  apply wholeAddition μ a.bundles addition remaining a.residue a.active f remaining.history hfix hfrozen
  · intro j
    apply (ha.1.separate j).mono_right
    rw [← hcover]
    exact (subset_iUnion (fun j => domain (addition j).cells) j).trans subset_union_left
  · exact hpair
  · exact hsep
  · exact hcover

include ha hfix hfrozen hadd hr hpair hsep hcover holdhist haddhist hactive in
theorem commit_committed : (commit a addition remaining f).Committed μ direction whole := by
  have ht := commitWholeAddition μ direction whole a ha addition remaining f hfix hfrozen hpair hsep hcover
  have hg := GlobalCompletion.whole_addition_preserves_EF_guard direction ht ha.2.2.2.1 ha.2.2.2.2 hactive
  refine ⟨commit_physical μ whole a ha.1 addition remaining f hadd hr hpair hsep hcover holdhist haddhist,
    ?_, ?_, hg.1, hg.2⟩
  · exact fun _ _ => measureReal_nonneg
  · exact fun _ => measureReal_nonneg

include ha hfix hfrozen hpair hsep hcover hactive in
theorem commit_target_counts (i : Fin n) :
    (R4GlobalPotential.targets (GlobalCompletion.margin direction (a.table μ).value) (a.table μ).residue i).card ≤
    (R4GlobalPotential.targets (GlobalCompletion.margin direction ((commit a addition remaining f).table μ).value)
      ((commit a addition remaining f).table μ).residue i).card := by
  exact GlobalCompletion.whole_addition_target_counts direction
    (commitWholeAddition μ direction whole a ha addition remaining f hfix hfrozen hpair hsep hcover)
    ha.2.2.2.1 ha.2.2.2.2 hactive i

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
