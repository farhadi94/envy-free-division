import EnvyFreeResearch.Full.UpperGlobalProtocolHistory
import EnvyFreeResearch.Full.UpperGlobalProtocolTerminal
import EnvyFreeResearch.Full.UpperBaseCasesProtocol

/-! The concrete one-cut base protocol committed to the original owners. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperEndpointCache
open UpperBaseCases UpperCircularStage
variable {n : ℕ}

def twoAgentTerminal (policy : Policy n) (chores : Bool) (a : Anchor n)
    (cutter chooser : Fin n) : Anchor n :=
  terminal a (cutAndChoose policy chores a.residue cutter chooser)
    (halfRun policy a.residue cutter).2.history

theorem twoAgent_terminal (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (policy : Policy n)
    (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (chores : Bool) (whole : Set ℝ) (a : Anchor n)
    (ha : a.Committed μ (if chores then .chore else .cake) whole)
    (hh : a.HistoryCompatible) (cutter chooser : Fin n)
    (hactive : a.active = {cutter,chooser}) (hne : chooser ≠ cutter)
    (hpositive : 0 < total a.residue cutter) :
    (twoAgentTerminal policy chores a cutter chooser).Committed μ
      (if chores then .chore else .cake) whole ∧
    (⋃ j, domain ((twoAgentTerminal policy chores a cutter chooser).bundles j).cells) = whole := by
  have hg := ha.1.residue_wellFormed
  have hp : 0 < (μ cutter).real (domain a.residue.cells) := by
    rw [← total_correct μ a.residue hg cutter]
    exact hpositive
  have hw := half_wellFormed μ policy hpolicy a.residue hg cutter hp
  obtain ⟨trace,_,htrace,_,_⟩ := half_executes policy a.residue cutter
  have hold : ∀ j, (a.bundles j).history ⊆ (halfRun policy a.residue cutter).2.history := by
    intro j x hx
    rw [htrace]
    exact List.mem_append_left _ (hh j hx)
  have hadd : ∀ j, (cutAndChoose policy chores a.residue cutter chooser j).history ⊆
      (halfRun policy a.residue cutter).2.history := by
    intro j
    have he := choice_history chores
      (leftState (halfRun policy a.residue cutter).2 ((halfRun policy a.residue cutter).1 0))
      (rightState (halfRun policy a.residue cutter).2 ((halfRun policy a.residue cutter).1 0))
      cutter chooser j rfl
    change (finish chores cutter chooser (halfRun policy a.residue cutter) j).history ⊆ _
    unfold finish
    rw [he]
    exact fun _ hx => hx
  have hfrozen : ∀ j ∉ a.active,
      domain (cutAndChoose policy chores a.residue cutter chooser j).cells = ∅ := by
    intro j hj
    have hn : j ∉ ({cutter,chooser} : Set (Fin n)) := by simpa [hactive] using hj
    unfold cutAndChoose finish
    rw [choice_frozen _ _ _ _ _ _ hn]
    rfl
  have hef : GlobalCompletion.ActiveEF (if chores then .chore else .cake)
      (value μ (cutAndChoose policy chores a.residue cutter chooser)) a.active := by
    change GlobalCompletion.ActiveEF (if chores then .chore else .cake)
      (fun i j => (μ i).real (domain (cutAndChoose policy chores a.residue cutter chooser j).cells)) a.active
    simpa only [hactive,Finset.coe_insert,Finset.coe_singleton] using
      cutAndChoose_EF μ policy hpolicy a.residue hg cutter chooser hp hne chores
  exact ⟨terminal_committed μ _ whole a ha _ _ hw.2.2.1
      (cutAndChoose_wellFormed μ policy hpolicy a.residue hg cutter chooser hp chores)
      (cutAndChoose_pairwise μ policy hpolicy a.residue hg cutter chooser hp chores)
      (cutAndChoose_complete μ policy hpolicy a.residue hg cutter chooser hp hne chores)
      hfrozen hold hadd hef,
    terminal_complete μ _ whole a ha _ _ hw.2.2.1
      (cutAndChoose_wellFormed μ policy hpolicy a.residue hg cutter chooser hp chores)
      (cutAndChoose_pairwise μ policy hpolicy a.residue hg cutter chooser hp chores)
      (cutAndChoose_complete μ policy hpolicy a.residue hg cutter chooser hp hne chores)
      hfrozen hold hadd hef⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
