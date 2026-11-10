import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolInitial
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalReceivedInvariant

/-! Enclosing query histories persist across all accepted and rejected
attempts, without changing the saved physical anchor on rejection. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperEndpointCache
variable {n : ℕ}

def Anchor.HistoryCompatible (a : Anchor n) : Prop :=
  ∀ j, (a.bundles j).history ⊆ a.residue.history

theorem initial_history (origin : State n) : (initial origin).HistoryCompatible :=
  fun _ => Subset.rfl

theorem commit_history (a : Anchor n) (addition : Fin n → State n) (remaining : State n)
    (f : Equiv.Perm (Fin n)) : (commit a addition remaining f).HistoryCompatible :=
  fun _ => Subset.rfl

/-- On rejected work only the enclosing transcript changes. -/
def refresh (a : Anchor n) (history : UpperCircularStage.History n) : Anchor n :=
  ⟨a.bundles,⟨a.residue.cells,history⟩,a.active⟩

theorem refresh_history (a : Anchor n) (history : UpperCircularStage.History n)
    (ha : a.HistoryCompatible) (hext : a.residue.history ⊆ history) :
    (refresh a history).HistoryCompatible := fun j _ hx => hext (ha j hx)

theorem refresh_table (μ : Fin n → Measure ℝ) (a : Anchor n)
    (history : UpperCircularStage.History n) : (refresh a history).table μ = a.table μ := rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem refresh_physical (whole : Set ℝ) (a : Anchor n) (ha : a.Physical μ whole)
    (history : UpperCircularStage.History n) (htruth : Truthful μ history)
    (hext : a.residue.history ⊆ history) : (refresh a history).Physical μ whole := by
  refine ⟨ha.bundles_wellFormed,?_,ha.pairwise,ha.separate,ha.cover⟩
  exact ⟨ha.residue_wellFormed.1,ha.residue_wellFormed.2.1,htruth,
    recordedHistory_mono _ ha.residue_wellFormed.2.2.2 hext⟩

theorem refresh_committed (direction : GlobalCompletion.Direction) (whole : Set ℝ)
    (a : Anchor n) (ha : a.Committed μ direction whole)
    (history : UpperCircularStage.History n) (htruth : Truthful μ history)
    (hext : a.residue.history ⊆ history) : (refresh a history).Committed μ direction whole :=
  ⟨refresh_physical μ whole a ha.1 history htruth hext,ha.2⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
