import EnvyFreeResearch.Full.UpperIdealPayments
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A concrete first-boundary floating step

A nonzero homogeneous direction supported on fractional coordinates has a
strictly positive finite first-boundary step. The step preserves every
linear equation, fixes all old integral coordinates, and strictly reduces
the number of fractional coordinates.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloatingStep

variable {Coord Equation : Type*} [Fintype Coord]

def fractional (x : Coord → ℝ) : Finset Coord :=
  Finset.univ.filter (fun c => 0 < x c ∧ x c < 1)

def moving (d : Coord → ℝ) : Finset Coord := Finset.univ.filter (fun c => d c ≠ 0)

theorem moving_nonempty (d : Coord → ℝ) (hd : d ≠ 0) : (moving d).Nonempty := by
  by_contra hn
  apply hd
  funext c
  have hc : c ∉ moving d := fun h => hn ⟨c, h⟩
  simpa [moving] using hc

def room (x d : Coord → ℝ) (c : Coord) : ℝ :=
  if 0 < d c then (1 - x c) / d c else -x c / d c

def stepLength (x d : Coord → ℝ) (hd : d ≠ 0) : ℝ :=
  (moving d).inf' (moving_nonempty d hd) (room x d)

def move (x d : Coord → ℝ) (hd : d ≠ 0) (c : Coord) : ℝ :=
  x c + stepLength x d hd * d c

omit [Fintype Coord] in
theorem room_positive (x d : Coord → ℝ) (c : Coord) (hd : d c ≠ 0)
    (hx : 0 < x c ∧ x c < 1) : 0 < room x d c := by
  by_cases hp : 0 < d c
  · exact (by simpa [room, hp] using div_pos (sub_pos.mpr hx.2) hp)
  · have hn : d c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hd
    exact (by simpa [room, hp] using div_pos_of_neg_of_neg (neg_neg_of_pos hx.1) hn)

theorem stepLength_positive (x d : Coord → ℝ) (hd : d ≠ 0)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1) : 0 < stepLength x d hd := by
  apply (Finset.lt_inf'_iff _).mpr
  intro c hc
  have hdc := (Finset.mem_filter.mp hc).2
  exact room_positive x d c hdc (hsupport c hdc)

theorem stepLength_le_room (x d : Coord → ℝ) (hd : d ≠ 0) (c : Coord) (hc : d c ≠ 0) :
    stepLength x d hd ≤ room x d c :=
  Finset.inf'_le _ (by simp [moving, hc])

/-- The first-boundary update is feasible in every coordinate. -/
theorem move_in_box (x d : Coord → ℝ) (hd : d ≠ 0)
    (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1) (c : Coord) :
    0 ≤ move x d hd c ∧ move x d hd c ≤ 1 := by
  have ht := (stepLength_positive x d hd hsupport).le
  by_cases hz : d c = 0
  · simpa [move, hz] using hbox c
  · have hroom := stepLength_le_room x d hd c hz
    by_cases hp : 0 < d c
    · rw [room, ite_eq_left hp] at hroom
      have hmul := (le_div_iff₀ hp).mp hroom
      have hnonneg := mul_nonneg ht hp.le
      dsimp only [move]
      constructor <;> linarith [hbox c]
    · have hn : d c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      rw [room, ite_eq_right hp] at hroom
      have hmul := (le_div_iff_of_neg hn).mp hroom
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos ht hn.le
      dsimp only [move]
      constructor <;> linarith [hbox c]

theorem move_fixed (x d : Coord → ℝ) (hd : d ≠ 0)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1) (c : Coord)
    (hnot : c ∉ fractional x) : move x d hd c = x c := by
  have hz : d c = 0 := by
    by_contra hne
    exact hnot (by simp [fractional, hsupport c hne])
  simp [move, hz]

theorem moving_coordinate_hits_boundary (x d : Coord → ℝ) (hd : d ≠ 0) :
    ∃ c, d c ≠ 0 ∧ (move x d hd c = 0 ∨ move x d hd c = 1) := by
  obtain ⟨c, hc, heq⟩ := Finset.exists_mem_eq_inf' (moving_nonempty d hd) (room x d)
  have hdc : d c ≠ 0 := (Finset.mem_filter.mp hc).2
  refine ⟨c, hdc, ?_⟩
  change x c + (moving d).inf' (moving_nonempty d hd) (room x d) * d c = 0 ∨ _
  rw [heq]
  by_cases hp : 0 < d c
  · right
    dsimp only [move, stepLength]
    rw [heq, room, ite_eq_left hp]
    field_simp
    ring
  · left
    rw [room, ite_eq_right hp]
    field_simp
    ring

theorem move_fractional_subset (x d : Coord → ℝ) (hd : d ≠ 0)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1) :
    fractional (move x d hd) ⊆ fractional x := by
  intro c hc
  by_contra hn
  have heq := move_fixed x d hd hsupport c hn
  exact hn (by simpa [fractional, heq] using hc)

/-- At least one previously fractional coordinate becomes integral, and
none of the old integral coordinates moves. -/
theorem move_decreases_fractional (x d : Coord → ℝ) (hd : d ≠ 0)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1) :
    (fractional (move x d hd)).card < (fractional x).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨move_fractional_subset x d hd hsupport, ?_⟩
  intro heq
  obtain ⟨c, hdc, hbound⟩ := moving_coordinate_hits_boundary x d hd
  have hold : c ∈ fractional x := by simp [fractional, hsupport c hdc]
  have hnew : c ∈ fractional (move x d hd) := by rw [heq]; exact hold
  rcases hbound with hbound | hbound <;> simp [fractional, hbound] at hnew

def linearValue (A : Equation → Coord → ℝ) (x : Coord → ℝ) (r : Equation) : ℝ :=
  ∑ c, A r c * x c

theorem move_preserves_equations (A : Equation → Coord → ℝ) (x d : Coord → ℝ) (hd : d ≠ 0)
    (hkernel : ∀ r, linearValue A d r = 0) (r : Equation) :
    linearValue A (move x d hd) r = linearValue A x r := by
  have hterm (c : Coord) : A r c * move x d hd c =
      A r c * x c + stepLength x d hd * (A r c * d c) := by dsimp [move]; ring
  simp only [linearValue, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  change linearValue A x r + stepLength x d hd * linearValue A d r = linearValue A x r
  rw [hkernel]
  simp

def Feasible (A : Equation → Coord → ℝ) (b : Equation → ℝ) (x : Coord → ℝ) : Prop :=
  (∀ c, 0 ≤ x c ∧ x c ≤ 1) ∧ ∀ r, linearValue A x r = b r

theorem move_feasible (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (x d : Coord → ℝ) (hd : d ≠ 0) (hx : Feasible A b x)
    (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1)
    (hkernel : ∀ r, linearValue A d r = 0) : Feasible A b (move x d hd) :=
  ⟨move_in_box x d hd hx.1 hsupport,
    fun r => (move_preserves_equations A x d hd hkernel r).trans (hx.2 r)⟩

/-- A feasible point with fewest fractional coordinates exists because the
number of such coordinates is a natural number. The following theorem
derives its kernel property using the explicit boundary step. -/
theorem exists_minimal_fractional (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (hfeasible : ∃ x, Feasible A b x) :
    ∃ x, Feasible A b x ∧ ∀ y, Feasible A b y → (fractional x).card ≤ (fractional y).card := by
  have hex : ∃ n : ℕ, ∃ x, Feasible A b x ∧ (fractional x).card = n := by
    obtain ⟨x, hx⟩ := hfeasible
    exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hx, hcard⟩ := Nat.find_spec hex
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [hcard]
  exact Nat.find_min' hex ⟨y, hy, rfl⟩

/-- Minimality rules out every nonzero supported kernel direction. -/
theorem minimal_kernel_trivial (A : Equation → Coord → ℝ) (b : Equation → ℝ)
    (x : Coord → ℝ) (hx : Feasible A b x)
    (hminimal : ∀ y, Feasible A b y → (fractional x).card ≤ (fractional y).card)
    (d : Coord → ℝ) (hsupport : ∀ c, d c ≠ 0 → 0 < x c ∧ x c < 1)
    (hkernel : ∀ r, linearValue A d r = 0) : d = 0 := by
  by_contra hd
  have hfeasible := move_feasible A b x d hd hx hsupport hkernel
  exact (not_lt_of_ge (hminimal _ hfeasible)) (move_decreases_fractional x d hd hsupport)

end EnvyFreeResearch.Full.UpperFloatingStep
