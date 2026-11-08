import EnvyFreeResearch.Full.ChoresCompletionSplit

/-! Query-free active-agent adapters retain the ambient original-observer
indexing while exposing the finite recipient lists used by completion. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open scoped Classical

variable {n k : ℕ}

def observerSet (agent : Fin k → Fin n) : Finset (Fin n) := Finset.univ.image agent

theorem observer_mem (agent : Fin k → Fin n) (i : Fin k) : agent i ∈ observerSet agent := by
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem observer_card (agent : Fin k → Fin n) : (observerSet agent).card ≤ k := by
  exact (Finset.card_image_le).trans_eq (by simp)

def extendAgent (agent : Fin k → Fin n) (hk : 0 < k) (i : ℕ) : Fin n :=
  if h : i < k then agent ⟨i,h⟩ else agent ⟨0,hk⟩

theorem extendAgent_fin (agent : Fin k → Fin n) (hk : 0 < k) (i : Fin k) :
    extendAgent agent hk i.val=agent i := by simp [extendAgent,i.isLt]

theorem split_budget_mono (a b k : ℕ) (hab : a ≤ b) : splitBudget a k ≤ splitBudget b k :=
  Nat.add_le_add_right (split_term_mono a b (countPieces k) hab) _

end EnvyFreeResearch.Full.Chores.Completion
