import EnvyFreeResearch.Full.UpperFloatingStep
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Floating with frozen integral coordinates and its rank certificate

The explicit boundary step from `UpperFloatingStep` is applied within the
face that fixes every original zero and one. A minimal fractional point has
no supported kernel direction; this yields the actual dimension inequality.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloating

open UpperFloatingStep

variable {Coord Equation : Type*} [Fintype Coord]

def Frozen (initial x : Coord → ℝ) : Prop :=
  ∀ c, initial c = 0 ∨ initial c = 1 → x c = initial c

def FrozenFeasible (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (initial x : Coord → ℝ) : Prop := Feasible A b x ∧ Frozen initial x

theorem exists_minimal_frozen (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (initial : Coord → ℝ) (hinitial : Feasible A b initial) :
    ∃ x, FrozenFeasible A b initial x ∧
      ∀ y, FrozenFeasible A b initial y → (fractional x).card ≤ (fractional y).card := by
  have hex : ∃ n : ℕ, ∃ x, FrozenFeasible A b initial x ∧ (fractional x).card = n :=
    ⟨_, initial, ⟨hinitial, fun _ _ => rfl⟩, rfl⟩
  obtain ⟨x, hx, hcard⟩ := Nat.find_spec hex
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [hcard]
  exact Nat.find_min' hex ⟨y, hy, rfl⟩

theorem minimal_frozen_kernel_trivial (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (initial x : Coord → ℝ) (hx : FrozenFeasible A b initial x)
    (hminimal : ∀ y, FrozenFeasible A b initial y → (fractional x).card ≤ (fractional y).card)
    (d : Coord → ℝ) (hsupport : ∀ c, d c ≠ 0 → c ∈ fractional x)
    (hkernel : ∀ r, linearValue A d r = 0) : d = 0 := by
  by_contra hd
  have hs : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1 := by
    intro c hc
    exact (Finset.mem_filter.mp (hsupport c hc)).2
  have hfeasible := move_feasible A b x d hd hx.1 hs hkernel
  have hfrozen : Frozen initial (move x d hd) := by
    intro c hc
    have hxc := hx.2 c hc
    have hnot : c ∉ fractional x := by
      rcases hc with hc | hc <;> simp [fractional, hxc, hc]
    exact (move_fixed x d hd hs c hnot).trans hxc
  exact (not_lt_of_ge (hminimal _ ⟨hfeasible, hfrozen⟩)) (move_decreases_fractional x d hd hs)


def NoFractionalKernel (A : Equation → Coord → ℝ) (x : Coord → ℝ) : Prop :=
  ∀ d : Coord → ℝ, (∀ c, d c ≠ 0 → c ∈ fractional x) →
    (∀ r, linearValue A d r = 0) → d = 0

theorem exists_frozen_basic (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (initial : Coord → ℝ) (hinitial : Feasible A b initial) :
    ∃ x, FrozenFeasible A b initial x ∧ NoFractionalKernel A x := by
  obtain ⟨x, hx, hminimal⟩ := exists_minimal_frozen A b initial hinitial
  exact ⟨x, hx, minimal_frozen_kernel_trivial A b initial x hx hminimal⟩

/-- Extend a vector on the fractional coordinates by zero. -/
def extendOn (S : Finset Coord) (d : S → ℝ) (c : Coord) : ℝ :=
  if h : c ∈ S then d ⟨c, h⟩ else 0

omit [Fintype Coord] in
theorem extendOn_support (S : Finset Coord) (d : S → ℝ) (c : Coord)
    (h : extendOn S d c ≠ 0) : c ∈ S := by
  by_contra hn
  exact h (by simp [extendOn, hn])

theorem sum_extendOn (S : Finset Coord) (d : S → ℝ) (f : Coord → ℝ) :
    (∑ c, f c * extendOn S d c) = ∑ c : S, f c * d c := by
  classical
  calc
    (∑ c, f c * extendOn S d c) = ∑ c ∈ S, f c * extendOn S d c := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro c _ hc
      simp [extendOn, hc]
    _ = ∑ c : S, f c * d c := by
      rw [← Finset.sum_coe_sort S (fun c => f c * extendOn S d c)]
      apply Finset.sum_congr rfl
      intro c _
      simp [extendOn, c.property]

/-- Kernel triviality for the actually free coordinates bounds their number
by the actual equation count. -/
theorem supported_kernel_card_bound [Fintype Equation] (A : Equation → Coord → ℝ)
    (S : Finset Coord)
    (hkernel : ∀ d : Coord → ℝ, (∀ c, d c ≠ 0 → c ∈ S) →
      (∀ r, linearValue A d r = 0) → d = 0) : S.card ≤ Fintype.card Equation := by
  let M : Matrix Equation S ℝ := fun r c => A r c
  have hinj : Function.Injective (Matrix.mulVecLin M) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    have hz : extendOn S d = 0 := hkernel (extendOn S d) (extendOn_support S d) (by
      intro r
      rw [linearValue, sum_extendOn]
      exact congrFun hd r)
    funext c
    have h := congrFun hz c
    simpa [extendOn, c.property] using h
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi] using hdim

end EnvyFreeResearch.Full.UpperFloating
