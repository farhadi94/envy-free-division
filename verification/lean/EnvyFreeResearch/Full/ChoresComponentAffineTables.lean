import EnvyFreeResearch.ChoreComposition

/-! Exact credit and deficit tables of closed affine batches. Every
assignment is installed, including zero-own and physically empty ones. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentAffine
open ChoreComposition R7Chores
open scoped Classical BigOperators

variable {Agent Root : Type*} [DecidableEq Agent]

def tasks (participants : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (label : Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) :
    List (Donation Agent Root) :=
  participants.toList.map (fun j => ⟨packages j,
    affineProposal (frames j) label j (owners j) (fun i => u i j)⟩)

theorem task_payments (participants : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (label : Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) (i p : Agent) :
    payments (tasks participants packages frames label owners u) i p =
      if i ∈ participants ∧ p = label then u i i else 0 := by
  unfold payments tasks total
  rw [List.map_map, Finset.sum_map_toList]
  let f := fun j => (affineProposal (frames j) label j (owners j) (fun a => u a j)).payment i p
  change (∑ j ∈ participants, f j) = _
  have hz : ∀ j ∈ participants, j ≠ i → f j = 0 := by
    intro j _ hji
    simp [f, affineProposal, Proposal.payment, Ne.symm hji]
  by_cases hi : i ∈ participants
  · have hs : (∑ j ∈ participants, f j) = f i := by
      apply Finset.sum_eq_single i
      · exact hz
      · intro hnot
        exact (hnot hi).elim
    rw [hs]
    simp [f, affineProposal, Proposal.payment, hi]
  · have hs : (∑ j ∈ participants, f j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply hz j hj
      intro heq
      exact hi (heq ▸ hj)
    rw [hs]
    simp [hi]

theorem task_extras (participants : Finset Agent) (packages : Agent → Package Agent Root)
    (frames : Agent → Frame Agent Root) (label : Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ) (i j p : Agent) :
    extras (tasks participants packages frames label owners u) i j p =
      if j ∈ participants ∧ p = label then clipped (u i j) else 0 := by
  unfold extras tasks total
  rw [List.map_map, Finset.sum_map_toList]
  let f := fun a => (affineProposal (frames a) label a (owners a) (fun k => u k a)).extra i j p
  change (∑ a ∈ participants, f a) = _
  have hz : ∀ a ∈ participants, a ≠ j → f a = 0 := by
    intro a _ haj
    simp [f, affineProposal, Proposal.extra, Ne.symm haj]
  by_cases hj : j ∈ participants
  · have hs : (∑ a ∈ participants, f a) = f j := by
      apply Finset.sum_eq_single j
      · exact hz
      · intro hnot
        exact (hnot hj).elim
    rw [hs]
    simp [f, affineProposal, Proposal.extra, hj]
  · have hs : (∑ a ∈ participants, f a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply hz a ha
      intro heq
      exact hj (heq ▸ ha)
    rw [hs]
    simp [hj]

theorem task_payment_coverage (participants : Finset Agent)
    (packages : Agent → Package Agent Root) (frames : Agent → Frame Agent Root) (label : Agent)
    (owners : Agent → Equiv.Perm Agent) (u : Agent → Agent → ℝ)
    (hnonnegative : ∀ i ∈ participants, 0 ≤ u i i)
    (hcompare : ∀ i ∈ participants, ∀ j ∈ participants, u i j ≤ u i i)
    (hprotected : ∀ i ∉ participants, ∀ j ∈ participants, u i j ≤ 0)
    (i j p : Agent) :
    extras (tasks participants packages frames label owners u) i j p ≤
      payments (tasks participants packages frames label owners u) i p := by
  rw [task_payments, task_extras]
  by_cases hp : p = label
  · simp only [hp, and_true]
    by_cases hi : i ∈ participants <;> by_cases hj : j ∈ participants
    · rw [ite_eq_left hi, ite_eq_left hj]
      exact affine_component_payment _ _ (hnonnegative i hi) (hcompare i hi j hj)
    · rw [ite_eq_left hi, ite_eq_right hj]
      exact hnonnegative i hi
    · rw [ite_eq_right hi, ite_eq_left hj]
      exact max_le le_rfl (hprotected i hi j hj)
    · rw [ite_eq_right hi, ite_eq_right hj]
  · simp only [hp, and_false, ite_false, le_refl]

end EnvyFreeResearch.Full.Chores.ComponentAffine
