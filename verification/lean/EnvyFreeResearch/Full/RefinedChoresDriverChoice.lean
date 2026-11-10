import EnvyFreeResearch.Full.RefinedChoresGroupExecution
import EnvyFreeResearch.Full.RefinedChoresDataMass
import EnvyFreeResearch.Full.RefinedChoresTerminalSelect
import EnvyFreeResearch.Full.ChoresOuterDriverBudget

/-! Query-free selection in the concrete root-local pool. The actual
physical mass and factorial capacity guarantee a normal or terminal cohort. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.QueryProgram
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)

abbrev CohortChoice := Group data normal original r H ⊕ TerminalGroup data normal original r H

def chooseCohort : Option (CohortChoice data normal original r H) :=
  if ht : Nonempty (TerminalGroup data normal original r H) then some (.inr (Classical.choice ht))
  else if hn : Nonempty (Group data normal original r H) then some (.inl (Classical.choice hn))
  else none

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (good : data.Good original cost r H)
include good

theorem chooseCohort_some (hclosed : data.closed = []) (hpool : Fintype.card RootId = RefinedChoresPool.poolSize n)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) : ∃ choice, chooseCohort data normal original r H = some choice := by
  have hex : Nonempty (CohortChoice data normal original r H) := by
    obtain ⟨cl,hcl⟩ := actual_class_available data original cost r H good normal hclosed hpool
    rcases cl with (⟨p,C,b⟩ | ⟨p,A,B⟩) | ⟨p,A⟩
    · obtain ⟨group⟩ := normal_group_exists data normal original r H p C b hcl hr hH
      exact ⟨.inl group⟩
    · obtain ⟨group⟩ := terminal_group_exists data normal original r H p (.inl (A,B)) hcl
      exact ⟨.inr group⟩
    · obtain ⟨group⟩ := terminal_group_exists data normal original r H p (.inr A) hcl
      exact ⟨.inr group⟩
  unfold chooseCohort
  split_ifs with ht hn
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · obtain ⟨choice⟩ := hex
    cases choice with
    | inl group => exact (hn ⟨group⟩).elim
    | inr group => exact (ht ⟨group⟩).elim

theorem chooseCohort_some_mass (hmass : data.activeMass = RefinedChoresPool.poolSize n)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) : ∃ choice, chooseCohort data normal original r H = some choice := by
  have hex : Nonempty (CohortChoice data normal original r H) := by
    obtain ⟨cl,hcl⟩ := actual_class_available_mass data original cost r H good normal hmass
    rcases cl with (⟨p,C,b⟩ | ⟨p,A,B⟩) | ⟨p,A⟩
    · obtain ⟨group⟩ := normal_group_exists data normal original r H p C b hcl hr hH
      exact ⟨.inl group⟩
    · obtain ⟨group⟩ := terminal_group_exists data normal original r H p (.inl (A,B)) hcl
      exact ⟨.inr group⟩
    · obtain ⟨group⟩ := terminal_group_exists data normal original r H p (.inr A) hcl
      exact ⟨.inr group⟩
  unfold chooseCohort
  split_ifs with ht hn
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · obtain ⟨choice⟩ := hex
    cases choice with
    | inl group => exact (hn ⟨group⟩).elim
    | inr group => exact (ht ⟨group⟩).elim

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.chooseCohort_some
