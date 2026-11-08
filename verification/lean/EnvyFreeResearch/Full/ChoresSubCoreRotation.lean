import EnvyFreeResearch.Full.ChoresSubCoreEqualValues

/-!
# Query-free physical reassignment along a SubCore owner chain

The operation changes only ownership. Every cached suffix record remains
literally unchanged. It consumes the equalities proved by the two chain walks
and produces an injective assignment, with the first parent newly assigned
and the final whole parent newly unused.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent : Type*}

def rotate {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (i : Agent) : Parent := by
  classical
  exact if hs : ∃ r, owners r = i then parents (Classical.choose hs).castSucc else assigned i

lemma rotate_path {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (r : Fin h) : rotate owners parents assigned (owners r) = parents r.castSucc := by
  classical
  have hs : ∃ j, owners j = owners r := ⟨r, rfl⟩
  have hi : Classical.choose hs = r := owners.injective (Classical.choose_spec hs)
  simp only [rotate, dite_eq_left hs, hi]

lemma rotate_outside {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (i : Agent) (hi : ∀ r, owners r ≠ i) :
    rotate owners parents assigned i = assigned i := by
  classical
  have hn : ¬ ∃ r, owners r = i := by simpa only [not_exists] using hi
  simp only [rotate, dite_eq_right hn]

lemma castSucc_parent_preimage {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (hfree : ∀ i, assigned i ≠ parents 0) (r : Fin h) (i : Agent)
    (heq : assigned i = parents r.castSucc) : ∃ k, owners k = i := by
  by_cases hr : r.val = 0
  · have hr0 : r.castSucc = 0 := Fin.ext hr
    exact (hfree i (heq.trans (congrArg parents hr0))).elim
  · let k : Fin h := ⟨r.val - 1, by omega⟩
    have hk : k.succ = r.castSucc := Fin.ext (by dsimp [k]; omega)
    exact ⟨k, assigned.injective ((hchain k).trans ((congrArg parents hk).trans heq.symm))⟩

theorem rotate_injective {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (hfree : ∀ i, assigned i ≠ parents 0) : Injective (rotate owners parents assigned) := by
  classical
  intro i j hij
  by_cases hi : ∃ r, owners r = i <;> by_cases hj : ∃ r, owners r = j
  · obtain ⟨r, rfl⟩ := hi
    obtain ⟨s, rfl⟩ := hj
    rw [rotate_path, rotate_path] at hij
    have hcast := parents.injective hij
    have hrs : r = s := Fin.ext (congrArg (fun q : Fin (h + 1) => q.val) hcast)
    exact congrArg owners hrs
  · obtain ⟨r, rfl⟩ := hi
    rw [rotate_path, rotate_outside _ _ _ j (by simpa only [not_exists] using hj)] at hij
    exact (hj (castSucc_parent_preimage owners parents assigned hchain hfree r j hij.symm)).elim
  · obtain ⟨s, rfl⟩ := hj
    rw [rotate_outside _ _ _ i (by simpa only [not_exists] using hi), rotate_path] at hij
    exact (hi (castSucc_parent_preimage owners parents assigned hchain hfree s i hij)).elim
  · rw [rotate_outside _ _ _ i (by simpa only [not_exists] using hi),
      rotate_outside _ _ _ j (by simpa only [not_exists] using hj)] at hij
    exact assigned.injective hij

def rotated {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (hfree : ∀ i, assigned i ≠ parents 0) : Agent ↪ Parent :=
  ⟨rotate owners parents assigned, rotate_injective owners parents assigned hchain hfree⟩

theorem old_parent_retained {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (i : Agent) (hlast : assigned i ≠ parents (Fin.last h)) :
    ∃ j, rotate owners parents assigned j = assigned i := by
  classical
  by_cases hi : ∃ r, owners r = i
  · obtain ⟨r, rfl⟩ := hi
    have hr : r.val + 1 < h := by
      by_contra hh
      have heq : r.succ = Fin.last h := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_last]
        have := r.isLt
        omega)
      exact hlast ((hchain r).trans (congrArg parents heq))
    let next : Fin h := ⟨r.val + 1, hr⟩
    refine ⟨owners next, ?_⟩
    rw [rotate_path, hchain]
    exact congrArg parents (Fin.ext rfl)
  · exact ⟨i, rotate_outside owners parents assigned i (by simpa only [not_exists] using hi)⟩

theorem last_parent_freed {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (hfree : ∀ i, assigned i ≠ parents 0) :
    ∀ i, rotate owners parents assigned i ≠ parents (Fin.last h) := by
  classical
  intro i heq
  by_cases hi : ∃ r, owners r = i
  · obtain ⟨r, rfl⟩ := hi
    rw [rotate_path] at heq
    have hv := congrArg (fun q : Fin (h + 1) => q.val) (parents.injective heq)
    have := r.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  · rw [rotate_outside _ _ _ i (by simpa only [not_exists] using hi)] at heq
    by_cases hh : h = 0
    · subst h
      exact hfree i heq
    · let last : Fin h := ⟨h - 1, by omega⟩
      have hl : last.succ = Fin.last h := Fin.ext (by dsimp [last]; omega)
      have howner : owners last = i := assigned.injective ((hchain last).trans
        ((congrArg parents hl).trans heq.symm))
      exact hi ⟨last, howner⟩

theorem new_unused_classification {h : ℕ} (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent)
    (assigned : Agent ↪ Parent) (hchain : ∀ r, assigned (owners r) = parents r.succ)
    (p : Parent) (hp : ∀ i, rotate owners parents assigned i ≠ p) :
    (∀ i, assigned i ≠ p) ∨ p = parents (Fin.last h) := by
  classical
  by_cases hlast : p = parents (Fin.last h)
  · exact Or.inr hlast
  · left
    intro i hi
    obtain ⟨j, hj⟩ := old_parent_retained owners parents assigned hchain i (by simpa only [hi] using hlast)
    exact hp j (hj.trans hi)

/-- The actual ownership rotation preserves global cake preference, all
benchmarks, and the physical whole-unused-parent invariant. Its parent states
are unchanged; the last whole parent is freed and the start becomes assigned. -/
theorem rotation_correct {h : ℕ} (hh : 0 < h)
    (owners : Fin h ↪ Agent) (parents : Fin (h + 1) ↪ Parent) (assigned : Agent ↪ Parent)
    (hchain : ∀ r, assigned (owners r) = parents r.succ) (hfree : ∀ i, assigned i ≠ parents 0)
    {Coord Value : Type*} [Preorder Value] (value : Agent → Parent → Coord → Value)
    (state cap : Parent → Coord) (benchmark : Agent → Value)
    (hbest : ∀ i p, value i p (state p) ≤ value i (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i, benchmark i ≤ value i (assigned i) (state (assigned i)))
    (hwhole : ∀ p, (∀ i, assigned i ≠ p) → state p = cap p)
    (hlast : state (parents (Fin.last h)) = cap (parents (Fin.last h)))
    (htie : ∀ r, value (owners r) (parents r.castSucc) (state (parents r.castSucc)) =
      value (owners r) (parents r.succ) (state (parents r.succ))) :
    let newAssignment := rotated owners parents assigned hchain hfree
    (∀ i p, value i p (state p) ≤ value i (newAssignment i) (state (newAssignment i))) ∧
    (∀ i, benchmark i ≤ value i (newAssignment i) (state (newAssignment i))) ∧
    (∀ p, (∀ i, newAssignment i ≠ p) → state p = cap p) ∧
    (∃ i, newAssignment i = parents 0) ∧ (∀ i, newAssignment i ≠ parents (Fin.last h)) := by
  classical
  dsimp only
  have hown : ∀ i, value i (rotate owners parents assigned i) (state (rotate owners parents assigned i)) =
      value i (assigned i) (state (assigned i)) := by
    intro i
    by_cases hi : ∃ r, owners r = i
    · obtain ⟨r, rfl⟩ := hi
      rw [rotate_path, hchain]
      exact htie r
    · rw [rotate_outside _ _ _ i (by simpa only [not_exists] using hi)]
  refine ⟨?_, ?_, ?_, ?_, last_parent_freed owners parents assigned hchain hfree⟩
  · intro i p
    change value i p (state p) ≤ value i (rotate owners parents assigned i) (state (rotate owners parents assigned i))
    rw [hown]
    exact hbest i p
  · intro i
    change benchmark i ≤ value i (rotate owners parents assigned i) (state (rotate owners parents assigned i))
    rw [hown]
    exact hbenchmark i
  · intro p hp
    rcases new_unused_classification owners parents assigned hchain p hp with hp | rfl
    · exact hwhole p hp
    · exact hlast
  · refine ⟨owners ⟨0, hh⟩, ?_⟩
    exact rotate_path owners parents assigned ⟨0, hh⟩

end EnvyFreeResearch.Full.Chores.SubCore
