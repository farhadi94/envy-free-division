import EnvyFreeResearch.Full.ChoresFrontierInvariant

/-! A root-local frontier invariant allowing one paid but unexecuted target.
Every old frontier lemma is recovered as soon as the target is inside its SCC.
The proof uses actual immutable atom ranks, not a synchronized partition. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresPendingFrontier
open Chores.Frontier
open scoped Classical
variable {n : ℕ}

structure Pending (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z : Fin n) : Prop where
  allowed_eligible : R ⊆ E
  allowed_internal_or_target : R ⊆ insert z C
  forbidden_internal : F ⊆ C
  allowed_forbidden : Disjoint R F
  frontier_eligible : z ∈ E
  frontier_allowed : z ∈ R
  higher_internal : ∀ i ∈ E, rank z < rank i → i ∈ C
  allowed_above : ∀ i ∈ R, rank z ≤ rank i
  passed_small : ∀ a : Fin n, rank z ≤ a.val → Small w r H a

theorem of_invariant (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z : Fin n)
    (h : Invariant w rank r H E C R F z) (hz : z ∈ R) :
    Pending w rank r H E C R F z :=
  ⟨h.allowed_eligible, fun _ hi => Finset.mem_insert_of_mem (h.allowed_internal hi),
    h.forbidden_internal, h.allowed_forbidden, h.frontier_eligible, hz,
    h.higher_internal, h.allowed_above, h.passed_small⟩

theorem at_sink (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z : Fin n)
    (h : Pending w rank r H E C R F z) (hz : z ∈ C) :
    Invariant w rank r H E C R F z := by
  refine ⟨h.allowed_eligible, ?_, h.forbidden_internal, h.allowed_forbidden,
    h.frontier_eligible, hz, h.higher_internal, h.allowed_above, h.passed_small⟩
  intro i hi
  rcases Finset.mem_insert.mp (h.allowed_internal_or_target hi) with rfl | hi
  · exact hz
  · exact hi

theorem grow (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C D R F : Finset (Fin n)) (z : Fin n)
    (h : Pending w rank r H E C R F z) (hCD : C ⊆ D) :
    Pending w rank r H E D R F z := by
  refine ⟨h.allowed_eligible, ?_, fun _ hi => hCD (h.forbidden_internal hi),
    h.allowed_forbidden, h.frontier_eligible, h.frontier_allowed,
    fun i hi hh => hCD (h.higher_internal i hi hh), h.allowed_above, h.passed_small⟩
  intro i hi
  rcases Finset.mem_insert.mp (h.allowed_internal_or_target hi) with rfl | hi
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hCD hi)

theorem pay (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C R F : Finset (Fin n)) (z q : Fin n)
    (h : Invariant w rank r H E C R F z)
    (hstop : (Stop.outside q).Valid rank E C)
    (hsmall : ∀ a : Fin n, rank q ≤ a.val → Small w r H a) :
    Pending w rank r H E C (insert q R) (F ∪ (C \ R)) q := by
  have hb := outside_update w rank r H E C R F (insert q C) z q h hstop hsmall
    (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
  refine ⟨hb.allowed_eligible, hb.allowed_internal, ?_, hb.allowed_forbidden,
    hb.frontier_eligible, Finset.mem_insert_self _ _, ?_, hb.allowed_above, hb.passed_small⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h.forbidden_internal hi
    · exact (Finset.mem_sdiff.mp hi).1
  · intro i hi hh
    exact before_stop_internal rank E C (.outside q) hstop i hi hh

/-- When a later graph update absorbs the paid target, the original full
frontier invariant is restored without another payment or a geometric cut. -/
theorem absorb (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E C D R F : Finset (Fin n)) (z : Fin n)
    (h : Pending w rank r H E C R F z) (hCD : C ⊆ D) (hz : z ∈ D) :
    Invariant w rank r H E D R F z :=
  at_sink w rank r H E D R F z (grow w rank r H E C D R F z h hCD) hz

end EnvyFreeResearch.Full.RefinedChoresPendingFrontier

#print axioms EnvyFreeResearch.Full.RefinedChoresPendingFrontier.pay
#print axioms EnvyFreeResearch.Full.RefinedChoresPendingFrontier.absorb
