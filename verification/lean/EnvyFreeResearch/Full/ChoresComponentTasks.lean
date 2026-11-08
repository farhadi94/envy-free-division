import EnvyFreeResearch.Full.ChoresSchedulerPartition

/-! The actual participant set of a component-cycle payment call. -/

namespace EnvyFreeResearch.Full.Chores.Scheduler.Partition

open scoped BigOperators

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def component (P : Partition Agent) (p : Agent) : Finset Agent :=
  Finset.univ.filter (fun i => P.representative i = p)

def tasks (P : Partition Agent) (selected : Finset Agent) : Finset Agent :=
  Finset.univ.filter (fun i => P.representative i ∈ selected)

@[simp] theorem mem_component (P : Partition Agent) (p i : Agent) :
    i ∈ P.component p ↔ P.representative i = p := by simp [component]

@[simp] theorem mem_tasks (P : Partition Agent) (selected : Finset Agent) (i : Agent) :
    i ∈ P.tasks selected ↔ P.representative i ∈ selected := by simp [tasks]

theorem owner_mem_component (P : Partition Agent) {p : Agent} (hp : p ∈ P.labels) :
    p ∈ P.component p := (mem_component P p p).mpr ((mem_labels P p).mp hp)

theorem components_disjoint (P : Partition Agent) {p q : Agent} (hpq : p ≠ q) :
    Disjoint (P.component p) (P.component q) := by
  apply Finset.disjoint_left.mpr
  intro i hip hiq
  exact hpq (((P.mem_component p i).mp hip).symm.trans ((P.mem_component q i).mp hiq))

theorem tasks_eq_union (P : Partition Agent) (selected : Finset Agent) :
    P.tasks selected = selected.biUnion P.component := by
  ext i
  simp only [mem_tasks, Finset.mem_biUnion, mem_component]
  exact ⟨fun h => ⟨P.representative i, h, rfl⟩, fun ⟨p, hp, heq⟩ => heq.symm ▸ hp⟩

theorem tasks_card (P : Partition Agent) (selected : Finset Agent) :
    (P.tasks selected).card = ∑ p ∈ selected, (P.component p).card := by
  rw [tasks_eq_union]
  exact Finset.card_biUnion (fun p _ q _ hpq => P.components_disjoint hpq)

theorem tasks_nonempty (P : Partition Agent) (selected : Finset Agent)
    (hsub : selected ⊆ P.labels) (hne : selected.Nonempty) : (P.tasks selected).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, (mem_tasks P selected p).mpr ?_⟩
  rwa [(P.mem_labels p).mp (hsub hp)]

theorem tasks_card_le (P : Partition Agent) (selected : Finset Agent) :
    (P.tasks selected).card ≤ Fintype.card Agent := Finset.card_le_univ _

theorem tasks_at_label (P : Partition Agent) (selected : Finset Agent) (p : Agent)
    (hp : p ∈ selected) :
    (P.tasks selected).filter (fun i => P.representative i = p) = P.component p := by
  ext i
  simp only [Finset.mem_filter, mem_tasks, mem_component]
  exact ⟨And.right, fun h => ⟨h.symm ▸ hp, h⟩⟩

theorem tasks_at_other_label (P : Partition Agent) (selected : Finset Agent) (p : Agent)
    (hp : p ∉ selected) :
    (P.tasks selected).filter (fun i => P.representative i = p) = ∅ := by
  ext i
  simp only [Finset.mem_filter, mem_tasks, Finset.notMem_empty, iff_false, not_and]
  intro hi heq
  exact hp (heq ▸ hi)

end EnvyFreeResearch.Full.Chores.Scheduler.Partition
