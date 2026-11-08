import EnvyFreeResearch.Full.ChoresComponentSurvivor

/-! Finite component labels, their actual merger, and protected representatives. -/

namespace EnvyFreeResearch.Full.Chores.Scheduler

open Components

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

structure Partition (Agent : Type*) where
  representative : Agent → Agent
  fixed : ∀ a, representative (representative a) = representative a

namespace Partition

def labels (P : Partition Agent) : Finset Agent := Finset.univ.image P.representative

@[simp] theorem mem_labels (P : Partition Agent) (a : Agent) :
    a ∈ P.labels ↔ P.representative a = a := by
  constructor
  · rintro ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact P.fixed x
  · intro ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩

theorem representative_mem (P : Partition Agent) (a : Agent) :
    P.representative a ∈ P.labels := (mem_labels P _).mpr (P.fixed a)

theorem labels_nonempty [Nonempty Agent] (P : Partition Agent) : P.labels.Nonempty := by
  exact ⟨P.representative (Classical.choice (inferInstance : Nonempty Agent)),
    P.representative_mem _⟩

theorem labels_card_le (P : Partition Agent) : P.labels.card ≤ Fintype.card Agent :=
  (Finset.card_image_le).trans_eq (Finset.card_univ)

def initial : Partition Agent := ⟨id, fun _ => rfl⟩

@[simp] theorem initial_labels : (initial : Partition Agent).labels = Finset.univ := by
  ext a
  simp [initial]

def collapse (selected : Finset Agent) (keep a : Agent) : Agent :=
  if a ∈ selected then keep else a

theorem collapse_eq_iff (selected : Finset Agent) (keep : Agent) (hk : keep ∈ selected)
    (a b : Agent) :
    collapse selected keep a = collapse selected keep b ↔
      a = b ∨ (a ∈ selected ∧ b ∈ selected) := by
  by_cases ha : a ∈ selected <;> by_cases hb : b ∈ selected <;>
    simp only [collapse, ha, hb, ite_true, ite_false]
  · simp [ha, hb]
  · constructor
    · intro h
      exact False.elim (hb (h ▸ hk))
    · rintro (rfl | ⟨_, h⟩) <;> contradiction
  · constructor
    · intro h
      exact False.elim (ha (h ▸ hk))
    · rintro (rfl | ⟨h, _⟩) <;> contradiction
  · simp [ha, hb]

def merge (P : Partition Agent) (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) : Partition Agent where
  representative a := collapse selected keep (P.representative a)
  fixed a := by
    have hkeep := (P.mem_labels keep).mp (hsub hk)
    by_cases ha : P.representative a ∈ selected
    · simp [collapse, ha, hkeep, hk]
    · simp [collapse, ha, P.fixed]

@[simp] theorem merge_representative (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) (a : Agent) :
    (P.merge selected keep hsub hk).representative a =
      collapse selected keep (P.representative a) := rfl

theorem merge_relation (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) (a b : Agent) :
    (P.merge selected keep hsub hk).representative a =
      (P.merge selected keep hsub hk).representative b ↔
    P.representative a = P.representative b ∨
      (P.representative a ∈ selected ∧ P.representative b ∈ selected) :=
  collapse_eq_iff _ _ hk _ _

theorem merge_labels (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) :
    (P.merge selected keep hsub hk).labels = insert keep (P.labels \ selected) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    change collapse selected keep (P.representative a) = x at ha
    by_cases hmem : P.representative a ∈ selected
    · simp only [collapse, ite_eq_left hmem] at ha
      exact Finset.mem_insert.mpr (Or.inl ha.symm)
    · simp only [collapse, ite_eq_right hmem] at ha
      subst x
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr
        ⟨P.representative_mem a, hmem⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · apply (mem_labels _ _).mpr
      have hkeep := (P.mem_labels x).mp (hsub hk)
      simp [merge_representative, collapse, hkeep, hk]
    · obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
      apply (mem_labels _ _).mpr
      simp [merge_representative, collapse, (P.mem_labels x).mp hx, hnot]

theorem merge_card (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) :
    (P.merge selected keep hsub hk).labels.card + selected.card = P.labels.card + 1 := by
  rw [merge_labels, Finset.card_insert_of_notMem (by simp [hk])]
  have h := Finset.card_sdiff_add_card_eq_card hsub
  omega

theorem merge_decreases (P : Partition Agent) (selected : Finset Agent)
    (keep : Agent) (hsub : selected ⊆ P.labels) (hk : keep ∈ selected)
    (htwo : 2 ≤ selected.card) :
    (P.merge selected keep hsub hk).labels.card < P.labels.card := by
  have h := P.merge_card selected keep hsub hk
  omega

noncomputable def keepLabel (protectedLabel : Agent) (selected : Finset Agent)
    (hne : selected.Nonempty) : Agent :=
  if protectedLabel ∈ selected then protectedLabel else hne.choose

theorem keepLabel_mem (protectedLabel : Agent) (selected : Finset Agent)
    (hne : selected.Nonempty) : keepLabel protectedLabel selected hne ∈ selected := by
  by_cases hp : protectedLabel ∈ selected
  · simp [keepLabel, hp]
  · simpa [keepLabel, hp] using hne.choose_spec

theorem merge_protected (P : Partition Agent) (selected : Finset Agent)
    (hsub : selected ⊆ P.labels) (hne : selected.Nonempty) (protectedLabel : Agent)
    (hp : P.representative protectedLabel = protectedLabel) :
    (P.merge selected (keepLabel protectedLabel selected hne) hsub
      (keepLabel_mem _ _ _)).representative protectedLabel = protectedLabel := by
  by_cases hmem : protectedLabel ∈ selected <;>
    simp [merge_representative, collapse, hp, keepLabel, hmem]

end Partition

end EnvyFreeResearch.Full.Chores.Scheduler
