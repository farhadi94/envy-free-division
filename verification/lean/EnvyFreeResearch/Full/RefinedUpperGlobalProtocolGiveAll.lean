import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTerminal
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolHistory

/-! Concrete terminal zero/singleton branches at globally committed anchors. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperEndpointCache UpperZeroRows
variable {n : ℕ}

def giveAllTerminal (a : Anchor n) (recipient : Fin n) : Anchor n :=
  terminal a (giveAll a.residue recipient) a.residue.history

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (direction : GlobalCompletion.Direction)
  (whole : Set ℝ) (a : Anchor n) (ha : a.Committed μ direction whole)
  (hh : a.HistoryCompatible) (recipient : Fin n) (hrecipient : recipient ∈ a.active)

include ha hh hrecipient in
theorem giveAll_terminal
    (hef : GlobalCompletion.ActiveEF direction (value μ (giveAll a.residue recipient)) a.active) :
    (giveAllTerminal a recipient).Committed μ direction whole ∧
      (⋃ j, domain ((giveAllTerminal a recipient).bundles j).cells) = whole := by
  have hfrozen : ∀ j ∉ a.active, domain (giveAll a.residue recipient j).cells = ∅ := by
    intro j hj
    rw [giveAll_domain,ite_eq_right]
    intro h
    exact hj (h ▸ hrecipient)
  have hist (j : Fin n) : (giveAll a.residue recipient j).history ⊆ a.residue.history := by
    rw [giveAll_history]
  exact ⟨terminal_committed μ direction whole a ha _ _ ha.1.residue_wellFormed.2.2.1
      (giveAll_wellFormed μ a.residue ha.1.residue_wellFormed recipient)
      (giveAll_pairwise a.residue recipient) (giveAll_complete a.residue recipient) hfrozen hh hist hef,
    terminal_complete μ direction whole a ha _ _ ha.1.residue_wellFormed.2.2.1
      (giveAll_wellFormed μ a.residue ha.1.residue_wellFormed recipient)
      (giveAll_pairwise a.residue recipient) (giveAll_complete a.residue recipient) hfrozen hh hist hef⟩

omit direction ha in
include hh hrecipient in
theorem chore_zero_terminal (ha : a.Committed μ .chore whole)
    (hz : total a.residue recipient = 0) :
    (giveAllTerminal a recipient).Committed μ .chore whole ∧
      (⋃ j, domain ((giveAllTerminal a recipient).bundles j).cells) = whole := by
  have hzero : (μ recipient).real (domain a.residue.cells) = 0 := by
    rw [← total_correct μ a.residue ha.1.residue_wellFormed recipient]
    exact hz
  exact giveAll_terminal μ .chore whole a ha hh recipient hrecipient
    (giveAll_chore_EF μ a.residue recipient hzero a.active)

omit direction ha in
include hh hrecipient in
theorem cake_all_zero_terminal (ha : a.Committed μ .cake whole)
    (hz : ∀ i ∈ a.active, total a.residue i = 0) :
    (giveAllTerminal a recipient).Committed μ .cake whole ∧
      (⋃ j, domain ((giveAllTerminal a recipient).bundles j).cells) = whole := by
  apply giveAll_terminal μ .cake whole a ha hh recipient hrecipient
  apply giveAll_cake_EF μ a.residue recipient a.active
  intro i hi
  rw [← total_correct μ a.residue ha.1.residue_wellFormed i]
  exact hz i hi

include ha hh hrecipient in
theorem singleton_terminal (hactive : a.active = {recipient}) :
    (giveAllTerminal a recipient).Committed μ direction whole ∧
      (⋃ j, domain ((giveAllTerminal a recipient).bundles j).cells) = whole := by
  apply giveAll_terminal μ direction whole a ha hh recipient hrecipient
  rw [hactive]
  change GlobalCompletion.ActiveEF direction
    (fun i j => (μ i).real (domain (giveAll a.residue recipient j).cells))
    (↑({recipient} : Finset (Fin n)))
  simpa only [Finset.coe_singleton] using giveAll_singleton_EF μ a.residue recipient direction

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
