import EnvyFreeResearch.Full.UpperGlobalPhysicalReceived

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (a : Anchor n)
  (ha : a.Physical μ whole) (output addition : Fin n → State n) (remaining : State n)
  (f : Equiv.Perm (Fin n))
  (hlabel : ∀ j, domain (output (f j)).cells = domain (a.bundles j).cells ∪ domain (addition j).cells)
  (hpair : Pairwise (fun i j => Disjoint (domain (addition i).cells) (domain (addition j).cells)))
  (hsep : ∀ j, Disjoint (domain (addition j).cells) (domain remaining.cells))
  (hcover : (⋃ j, domain (addition j).cells) ∪ domain remaining.cells = domain a.residue.cells)
  (hfix : ∀ j ∉ a.active, f j = j)
  (hfrozen : ∀ j ∉ a.active, domain (addition j).cells = ∅)
include ha hlabel hpair hsep hcover hfix hfrozen

def receivedWholeAddition : GlobalCompletion.WholeAddition (a.table μ).value
    ((received a output remaining).table μ).value (a.table μ).active
    (a.table μ).residue ((received a output remaining).table μ).residue where
  permutation := f
  addition := value μ addition
  addition_nonnegative := fun _ _ => measureReal_nonneg
  fixed := hfix
  frozen_addition := by intro i j hj; simp [value,hfrozen j hj]
  value_identity := by
    intro i j
    change (μ i).real (domain (output (f j)).cells) = _
    rw [hlabel]
    apply measureReal_union _ (domain_measurable _)
    apply (ha.separate j).mono_right
    rw [← hcover]
    exact (subset_iUnion (fun j => domain (addition j).cells) j).trans subset_union_left
  mass_partition := fun i => partition_mass (μ i) addition remaining a.residue hpair hsep hcover
  remaining_nonnegative := fun _ => measureReal_nonneg

theorem received_committed (direction : GlobalCompletion.Direction)
    (hvalid : GlobalCompletion.Valid direction (a.table μ))
    (hout : ∀ j, WellFormed μ (output j)) (hr : WellFormed μ remaining)
    (hactive : GlobalCompletion.ActiveEF direction (value μ output) a.active) :
    (received a output remaining).Committed μ direction whole := by
  have ht := receivedWholeAddition μ whole a ha output addition remaining f hlabel hpair hsep hcover hfix hfrozen
  have hg := GlobalCompletion.whole_addition_preserves_EF_guard direction ht hvalid.2.2.1 hvalid.2.2.2 hactive
  exact ⟨received_physical μ whole a ha output addition remaining f hlabel hpair hsep hcover hout hr,
    (fun _ _ => measureReal_nonneg),(fun _ => measureReal_nonneg),hg.1,hg.2⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
