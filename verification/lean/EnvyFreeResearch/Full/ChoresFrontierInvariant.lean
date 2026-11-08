import EnvyFreeResearch.Full.ChoresFrontierAtomic

/-! The mutable frontier invariant is preserved by the actual outside
proposal. The component merger may enlarge the component, but no other
change is assumed. Atomic extraction retains its large original atom in
every old allowed equalizer. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical

variable {n : ℕ}

structure Invariant (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z : Fin n) : Prop where
  allowed_eligible : R ⊆ E
  allowed_internal : R ⊆ C
  forbidden_internal : F ⊆ C
  allowed_forbidden : Disjoint R F
  frontier_eligible : z ∈ E
  frontier_internal : z ∈ C
  higher_internal : ∀ i ∈ E, rank z < rank i → i ∈ C
  allowed_above : ∀ i ∈ R, rank z ≤ rank i
  passed_small : ∀ a : Fin n, rank z ≤ a.val → Small w r H a

theorem outside_before_frontier (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z q : Fin n)
    (hinv : Invariant w rank r H E C R F z) (hq : q ∈ E \ C) : rank q ≤ rank z := by
  by_contra h
  exact (Finset.mem_sdiff.mp hq).2
    (hinv.higher_internal q (Finset.mem_sdiff.mp hq).1 (lt_of_not_ge h))

theorem outside_update (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F C' : Finset (Fin n)) (z q : Fin n)
    (hinv : Invariant w rank r H E C R F z)
    (hstop : (Stop.outside q).Valid rank E C)
    (hsmall : ∀ a : Fin n, rank q ≤ a.val → Small w r H a)
    (hC : C ⊆ C') (hqC : q ∈ C') :
    Invariant w rank r H E C' (insert q R) (F ∪ (C \ R)) q := by
  have hqE := (Finset.mem_sdiff.mp hstop.1).1
  have hqnot := (Finset.mem_sdiff.mp hstop.1).2
  have hqz := outside_before_frontier w rank r H E C R F z q hinv hstop.1
  refine ⟨?_,?_,?_,?_,hqE,hqC,?_,?_,hsmall⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact hi ▸ hqE
    · exact hinv.allowed_eligible hi
  · intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact hi ▸ hqC
    · exact hC (hinv.allowed_internal hi)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hC (hinv.forbidden_internal hi)
    · exact hC (Finset.mem_sdiff.mp hi).1
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hqnot (hinv.forbidden_internal hj)
      · exact hqnot (Finset.mem_sdiff.mp hj).1
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.disjoint_left.mp hinv.allowed_forbidden hi hj
      · exact (Finset.mem_sdiff.mp hj).2 hi
  · intro i hi hrank
    exact hC (before_stop_internal rank E C (.outside q) hstop i hi hrank)
  · intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i; exact le_rfl
    · exact hqz.trans (hinv.allowed_above i hi)

theorem atomic_allowed (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (C R F : Finset (Fin n)) (z : Fin n)
    (hinv : Invariant w rank r H (eligible w rank r H) C R F z)
    (t : ℕ) (a : Fin n) (hscan : largestBad w r H t=some a) :
    R ⊆ atomicParticipants (eligible w rank r H) rank a := by
  have ha := atomic_before_frontier w r H t (rank z) hinv.passed_small a hscan
  intro i hi
  exact Finset.mem_filter.mpr ⟨hinv.allowed_eligible hi,
    Nat.succ_le_of_lt (ha.trans_le (hinv.allowed_above i hi))⟩

theorem initial_invariant (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (owner : Fin n) (howner : rank owner=n)
    (hrank : ∀ i, rank i ≤ n) (hr : 0 ≤ r owner) (hH : 0 < H) :
    Invariant w rank r H (eligible w rank r H) {owner} {owner} ∅ owner := by
  refine ⟨?_,Finset.Subset.refl _,Finset.empty_subset _,by simp,
    owner_eligible w rank r H owner howner hr hH,by simp,?_,?_,?_⟩
  · intro i hi
    have hi : i=owner := Finset.mem_singleton.mp hi
    subst i
    exact owner_eligible w rank r H owner howner hr hH
  · intro i hi hgreater
    have hle := hrank i
    rw [howner] at hgreater
    omega
  · intro i hi
    have hi : i=owner := Finset.mem_singleton.mp hi
    subst i
    exact le_rfl
  · intro a ha
    rw [howner] at ha
    exact (not_le_of_gt a.isLt ha).elim

end EnvyFreeResearch.Full.Chores.Frontier
