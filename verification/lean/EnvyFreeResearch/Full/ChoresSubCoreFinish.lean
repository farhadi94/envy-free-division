import EnvyFreeResearch.Full.ChoresSubCoreWhileStep

/-!
# Completing a contested SubCore stage

Once every contested parent is assigned, the sole outside participant gets
an actual favorite uncontested whole parent. The target bounds establish
every cross comparison, and the new whole-parent certificate is literal.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent Coord Value : Type*} [DecidableEq Agent] [DecidableEq Parent]
    [LinearOrder Value]

theorem finish_contested_stage (selected : Finset Agent) (contested : Finset Parent)
    (assigned : selected ↪ Parent) (i : Agent) (p : Parent)
    (hi : i ∉ selected) (hp : p ∉ contested)
    (hfilled : ∀ q, q ∈ contested ↔ ∃ j, assigned j = q)
    (value : Agent → Parent → Coord → Value) (state whole : Parent → Coord)
    (benchmark target : Agent → Value)
    (houtside : ∀ q, q ∉ contested → state q = whole q)
    (hcontested : ∀ j : selected, ∀ q ∈ contested,
      value j.val q (state q) ≤ value j.val (assigned j) (state (assigned j)))
    (hown : ∀ j : selected, target j.val ≤ value j.val (assigned j) (state (assigned j)))
    (hbenchmark : ∀ j : selected, benchmark j.val ≤ value j.val (assigned j) (state (assigned j)))
    (houtsideTarget : ∀ j : selected, ∀ q, q ∉ contested → value j.val q (whole q) ≤ target j.val)
    (hnewContested : ∀ q ∈ contested, value i q (state q) ≤ target i)
    (hnewOutside : ∀ q, q ∉ contested → value i q (whole q) ≤ target i)
    (hfavorite : value i p (whole p) = target i) (hnewBenchmark : benchmark i ≤ target i) :
    ∃ newAssignment : ↑(insert i selected) ↪ Parent,
      (∀ j : ↑(insert i selected), ∀ q, value j.val q (state q) ≤
        value j.val (newAssignment j) (state (newAssignment j))) ∧
      (∀ j : ↑(insert i selected), benchmark j.val ≤ value j.val (newAssignment j) (state (newAssignment j))) ∧
      (∀ q, (∀ j, newAssignment j ≠ q) → state q = whole q) ∧
      newAssignment ⟨i, Finset.mem_insert_self _ _⟩ = p ∧ state p = whole p := by
  have hfree : ∀ j, assigned j ≠ p := fun j h => hp ((hfilled p).mpr ⟨j, h⟩)
  have hbest : ∀ j : selected, ∀ q, value j.val q (state q) ≤
      value j.val (assigned j) (state (assigned j)) := by
    intro j q
    by_cases hq : q ∈ contested
    · exact hcontested j q hq
    · rw [houtside q hq]
      exact (houtsideTarget j q hq).trans (hown j)
  have hwhole : ∀ q, (∀ j, assigned j ≠ q) → state q = whole q := by
    intro q hq
    apply houtside q
    intro hc
    obtain ⟨j, hj⟩ := (hfilled q).mp hc
    exact hq j hj
  have hnew : ∀ q, value i q (state q) ≤ value i p (state p) := by
    intro q
    rw [houtside p hp, hfavorite]
    by_cases hq : q ∈ contested
    · exact hnewContested q hq
    · rw [houtside q hq]
      exact hnewOutside q hq
  have hnewBench : benchmark i ≤ value i p (state p) := by
    rw [houtside p hp, hfavorite]
    exact hnewBenchmark
  obtain ⟨_, hbest', hbench', hwhole', howner, _⟩ :=
    grow_selected selected assigned i p hi hfree value state whole benchmark hbest hbenchmark hwhole hnew hnewBench
  exact ⟨insertedAssignment selected assigned i p hfree, hbest', hbench', hwhole', howner, houtside p hp⟩

variable [Fintype Parent] [Nonempty Parent]

def favoriteWhole (wholeValue : Agent → Parent → Value) (i : Agent) : Parent :=
  Classical.choose (Finset.exists_max_image Finset.univ (wholeValue i) Finset.univ_nonempty)

theorem favoriteWhole_spec (wholeValue : Agent → Parent → Value) (i : Agent) :
    ∀ p, wholeValue i p ≤ wholeValue i (favoriteWhole wholeValue i) :=
  fun p => (Classical.choose_spec (Finset.exists_max_image Finset.univ (wholeValue i) Finset.univ_nonempty)).2 p
    (Finset.mem_univ p)

/-- The favorite whole always meets an inherited benchmark, without assuming
that the benchmark or parent utilities are nonnegative. -/
theorem favorite_meets_inherited {Coord : Type*} [Preorder Coord]
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (i : Agent) (p : Parent) (x : Coord) (hx : x ∈ feasible) (hxcap : x ≤ whole p)
    (benchmark : Value) (hvalue : benchmark = value i p x) :
    benchmark ≤ value i (favoriteWhole (fun i p => value i p (whole p)) i)
      (whole (favoriteWhole (fun i p => value i p (whole p)) i)) := by
  rw [hvalue]
  exact ((hmono i p) hx (hwhole p) hxcap).trans (favoriteWhole_spec (fun i p => value i p (whole p)) i p)

/-- A benchmark above every uncontested whole forces its inherited parent
to be contested. This is the geometric part of the tie-rule necessity. -/
theorem inherited_parent_contested {Coord : Type*} [Preorder Coord]
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (contested : Finset Parent) (i : Agent) (p : Parent) (x : Coord)
    (hx : x ∈ feasible) (hxcap : x ≤ whole p) (benchmark : Value)
    (hvalue : benchmark = value i p x)
    (hstrict : ∀ q, q ∉ contested → value i q (whole q) < benchmark) : p ∈ contested := by
  by_contra hp
  have hlarge : benchmark ≤ value i p (whole p) := hvalue.le.trans ((hmono i p) hx (hwhole p) hxcap)
  exact (not_lt_of_ge hlarge) (hstrict p hp)

end EnvyFreeResearch.Full.Chores.SubCore
