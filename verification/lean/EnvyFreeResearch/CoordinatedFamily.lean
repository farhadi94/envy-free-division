import EnvyFreeResearch.MixedApproximation

/-! Finite certificates for the pure-leftmost moving-frontier construction.
Two agents distinct from the whole-tail owner suffice. Their per-cell
coefficients are nonpositive, so their signed envy comparisons sum to at
least `2 * α`, even with arbitrary fractional sharing of resolved cells.
This file does not formalize continuous density updates, first-root replay,
measurable tape selection, or the complete randomized lower bound. -/
namespace EnvyFreeResearch.CoordinatedFamily
open scoped BigOperators

def PairCoefficients (α a b : ℝ) : Prop :=
  (1 + α) * a + α * b ≤ 0 ∧ α * a + (1 + α) * b ≤ 0 ∧ a + b ≤ 0

def PairCellCondition (α a b : ℝ) : Prop :=
  (a ≤ 0 ∧ b ≤ 0) ∨
  (0 ≤ a ∧ b ≤ -((1 + α) / α) * a) ∨
  (0 ≤ b ∧ a ≤ -((1 + α) / α) * b)

theorem nonpositive_pair_coefficients {α a b : ℝ}
    (hα : 0 ≤ α) (ha : a ≤ 0) (hb : b ≤ 0) : PairCoefficients α a b := by
  have hαa := mul_nonpos_of_nonneg_of_nonpos hα ha
  have hαb := mul_nonpos_of_nonneg_of_nonpos hα hb
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem dominated_pair_coefficients {α a b : ℝ}
    (hα : 0 < α) (ha : 0 ≤ a)
    (hb : b ≤ -((1 + α) / α) * a) : PairCoefficients α a b := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hid : α * (-((1 + α) / α) * a) = -(1 + α) * a := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hα)
  rw [hid] at hmul
  have hab : a + b ≤ 0 := by
    by_contra h
    have hp := mul_pos hα (lt_of_not_ge h)
    nlinarith
  have hb0 : b ≤ 0 := by linarith
  have hs := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hα) hab
  exact ⟨by nlinarith, by nlinarith, hab⟩

theorem cell_condition_coefficients {α a b : ℝ}
    (hα : 0 < α) (hcell : PairCellCondition α a b) : PairCoefficients α a b := by
  rcases hcell with h | h | h
  · exact nonpositive_pair_coefficients (le_of_lt hα) h.1 h.2
  · exact dominated_pair_coefficients hα h.1 h.2
  · obtain ⟨hba, hab, hs⟩ := dominated_pair_coefficients hα h.1 h.2
    exact ⟨by nlinarith, by nlinarith, by linarith⟩

/-- Fractions x,y,z,r belong to the selected two nonowners, the tail owner,
and all remaining owners, respectively. -/
theorem cell_transfer_nonpositive {α a b x y z r : ℝ}
    (hα : 0 ≤ α) (hcoeff : PairCoefficients α a b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 ≤ r)
    (hsum : x + y + z + r = 1) :
    α * (a + b) * (1 - z) + a * x + b * y ≤ 0 := by
  obtain ⟨hfirst, hsecond, hpair⟩ := hcoeff
  have h1 := mul_nonpos_of_nonpos_of_nonneg hfirst hx
  have h2 := mul_nonpos_of_nonpos_of_nonneg hsecond hy
  have h3 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hα hpair) hr
  have hid : α * (a + b) * (1 - z) + a * x + b * y =
      ((1 + α) * a + α * b) * x +
      (α * a + (1 + α) * b) * y + α * (a + b) * r := by
    have hz : 1 - z = x + y + r := by linarith
    rw [hz]
    ring
  rw [hid]
  linarith

/-- Cell values already include each physical cell length. -/
theorem two_nonowners_envy_sum {Cell : Type*} (cells : Finset Cell)
    (α : ℝ) (a b x y z r : Cell → ℝ) (hα : 0 ≤ α)
    (hcoeff : ∀ k ∈ cells, PairCoefficients α (a k) (b k))
    (hx : ∀ k ∈ cells, 0 ≤ x k) (hy : ∀ k ∈ cells, 0 ≤ y k)
    (hr : ∀ k ∈ cells, 0 ≤ r k)
    (hsum : ∀ k ∈ cells, x k + y k + z k + r k = 1) :
    2 * α ≤
      (α * (1 - ∑ k ∈ cells, a k * (1 - z k)) - ∑ k ∈ cells, a k * x k) +
      (α * (1 - ∑ k ∈ cells, b k * (1 - z k)) - ∑ k ∈ cells, b k * y k) := by
  have htotal : ∑ k ∈ cells,
      (α * (a k + b k) * (1 - z k) + a k * x k + b k * y k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    exact cell_transfer_nonpositive hα (hcoeff k hk) (hx k hk)
      (hy k hk) (hr k hk) (hsum k hk)
  have hid : (∑ k ∈ cells,
      (α * (a k + b k) * (1 - z k) + a k * x k + b k * y k)) =
      α * (∑ k ∈ cells, a k * (1 - z k)) +
      α * (∑ k ∈ cells, b k * (1 - z k)) +
      (∑ k ∈ cells, a k * x k) + (∑ k ∈ cells, b k * y k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hid] at htotal
  linarith

theorem two_nonowners_force_violation {Cell : Type*} (cells : Finset Cell)
    (α ε : ℝ) (a b x y z r : Cell → ℝ) (hα : 0 ≤ α) (hε : ε < α)
    (hcoeff : ∀ k ∈ cells, PairCoefficients α (a k) (b k))
    (hx : ∀ k ∈ cells, 0 ≤ x k) (hy : ∀ k ∈ cells, 0 ≤ y k)
    (hr : ∀ k ∈ cells, 0 ≤ r k)
    (hsum : ∀ k ∈ cells, x k + y k + z k + r k = 1) :
    ε < α * (1 - ∑ k ∈ cells, a k * (1 - z k)) - ∑ k ∈ cells, a k * x k ∨
    ε < α * (1 - ∑ k ∈ cells, b k * (1 - z k)) - ∑ k ∈ cells, b k * y k := by
  have h := two_nonowners_envy_sum cells α a b x y z r hα hcoeff hx hy hr hsum
  by_contra hh
  push Not at hh
  linarith

/-- Direct composition from the profile's two-row cell condition to a failed
signed envy comparison. The preceding coefficient lemmas are all dependencies. -/
theorem cell_condition_force_violation {Cell : Type*} (cells : Finset Cell)
    (α ε : ℝ) (a b x y z r : Cell → ℝ) (hα : 0 < α) (hε : ε < α)
    (hcell : ∀ k ∈ cells, PairCellCondition α (a k) (b k))
    (hx : ∀ k ∈ cells, 0 ≤ x k) (hy : ∀ k ∈ cells, 0 ≤ y k)
    (hr : ∀ k ∈ cells, 0 ≤ r k)
    (hsum : ∀ k ∈ cells, x k + y k + z k + r k = 1) :
    ε < α * (1 - ∑ k ∈ cells, a k * (1 - z k)) - ∑ k ∈ cells, a k * x k ∨
    ε < α * (1 - ∑ k ∈ cells, b k * (1 - z k)) - ∑ k ∈ cells, b k * y k := by
  exact two_nonowners_force_violation cells α ε a b x y z r (le_of_lt hα) hε
    (fun k hk => cell_condition_coefficients hα (hcell k hk)) hx hy hr hsum

#print axioms nonpositive_pair_coefficients
#print axioms dominated_pair_coefficients
#print axioms cell_condition_coefficients
#print axioms cell_transfer_nonpositive
#print axioms two_nonowners_envy_sum
#print axioms two_nonowners_force_violation
#print axioms cell_condition_force_violation
end EnvyFreeResearch.CoordinatedFamily
