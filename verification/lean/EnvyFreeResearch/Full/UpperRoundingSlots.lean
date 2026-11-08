import EnvyFreeResearch.Full.UpperRoundingHall
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Consecutive sorted-slot packing

Fractional cell masses occupy consecutive intervals. Their intersections
with unit slots are computed by differences of the clamped cumulative mass.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRounding

/-- Cumulative mass in a unit interval. -/
def clip (t : ℝ) : ℝ := min (max t 0) 1

theorem clip_nonneg (t : ℝ) : 0 ≤ clip t := le_min (le_max_right _ _) zero_le_one

theorem clip_le_one (t : ℝ) : clip t ≤ 1 := min_le_right _ _

theorem clip_mono : Monotone clip := fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

theorem clip_eq_zero {t : ℝ} (h : t ≤ 0) : clip t = 0 := by simp [clip, max_eq_right h]

theorem clip_eq_one {t : ℝ} (h : 1 ≤ t) : clip t = 1 := by
  simp [clip, max_eq_left (zero_le_one.trans h), min_eq_right h]

theorem clip_eq_ramps (t : ℝ) : clip t = max t 0 - max (t - 1) 0 := by
  unfold clip
  by_cases ht : t ≤ 0
  · rw [max_eq_right ht, max_eq_right (by linarith : t - 1 ≤ 0)]
    norm_num
  · rw [max_eq_left (le_of_not_ge ht)]
    by_cases ht' : t ≤ 1
    · rw [min_eq_left ht', max_eq_right (by linarith : t - 1 ≤ 0), sub_zero]
    · rw [min_eq_right (le_of_not_ge ht'), max_eq_left (by linarith : 0 ≤ t - 1)]
      ring

/-- The total of successive unit intersections is the original length. -/
theorem sum_clip (t : ℝ) (n : ℕ) (ht : 0 ≤ t) (htn : t ≤ n) :
    (∑ s ∈ Finset.range n, clip (t - s)) = t := by
  have heq (s : ℕ) : clip (t - s) = max (t - s) 0 - max (t - (s + 1 : ℕ)) 0 := by
    rw [clip_eq_ramps]
    push_cast
    congr 2; ring
  simp_rw [heq]
  rw [Finset.sum_range_sub']
  simp [max_eq_left ht, max_eq_right (sub_nonpos.mpr htn)]

/-- A tuple extended by zero, used only to simplify finite cumulative sums. -/
def extend {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then x ⟨i, h⟩ else 0

def cumulative {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := ∑ k ∈ Finset.range i, extend x k

@[simp] theorem cumulative_zero {n : ℕ} (x : Fin n → ℝ) : cumulative x 0 = 0 := by simp [cumulative]

@[simp] theorem extend_fin {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : extend x i = x i := by
  simp [extend, i.isLt]

theorem cumulative_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    cumulative x (i.val + 1) = cumulative x i + x i := by simp [cumulative, Finset.sum_range_succ]

theorem cumulative_total {n : ℕ} (x : Fin n → ℝ) : cumulative x n = ∑ i, x i := by
  simpa [cumulative, extend] using (Finset.sum_fin_eq_sum_range x).symm

theorem extend_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ℕ) :
    0 ≤ extend x i := by
  unfold extend
  split_ifs with h
  · exact hx _
  · exact le_rfl

theorem cumulative_mono {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : Monotone (cumulative x) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => extend_nonneg x hx k)

theorem cumulative_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ℕ) :
    0 ≤ cumulative x i := Finset.sum_nonneg (fun k _ => extend_nonneg x hx k)

/-- Fraction of cell `i` in unit slot `s`. -/
def slotMass {n : ℕ} (x : Fin n → ℝ) (s : ℕ) (i : Fin n) : ℝ :=
  clip (cumulative x (i.val + 1) - s) - clip (cumulative x i - s)

theorem slotMass_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (s : ℕ) (i : Fin n) : 0 ≤ slotMass x s i := by
  apply sub_nonneg.mpr
  apply clip_mono
  exact sub_le_sub_right (cumulative_mono x hx (Nat.le_succ _)) _

/-- Every slot has exactly its intersection with the total packed mass. -/
theorem slotMass_row {n : ℕ} (x : Fin n → ℝ) (s : ℕ) :
    (∑ i, slotMass x s i) = clip ((∑ i, x i) - s) := by
  simp only [slotMass]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => clip (cumulative x (i + 1) - s) - clip (cumulative x i - s))]
  rw [Finset.sum_range_sub (fun i => clip (cumulative x i - s)),
    cumulative_total, cumulative_zero]
  rw [clip_eq_zero (sub_nonpos.mpr (Nat.cast_nonneg s) : (0 : ℝ) - s ≤ 0), sub_zero]

/-- Slotting preserves each cell's fraction exactly. -/
theorem slotMass_column {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (N : ℕ) (hN : (∑ i, x i) ≤ N) (i : Fin n) :
    (∑ s ∈ Finset.range N, slotMass x s i) = x i := by
  have hp (r : ℕ) (hr : r ≤ n) : cumulative x r ≤ N :=
    (cumulative_mono x hx hr).trans ((cumulative_total x).le.trans hN)
  simp only [slotMass, Finset.sum_sub_distrib]
  rw [sum_clip _ N (cumulative_nonneg x hx _) (hp _ i.isLt),
    sum_clip _ N (cumulative_nonneg x hx _) (hp _ i.isLt.le), cumulative_succ]
  ring

/-- Positive overlap puts the cell's endpoints on opposite sides of the
corresponding unit slot boundaries. -/
theorem slotMass_positive_bounds {n : ℕ} (x : Fin n → ℝ) (s : ℕ) (i : Fin n)
    (h : 0 < slotMass x s i) :
    cumulative x i < (s : ℝ) + 1 ∧ (s : ℝ) < cumulative x (i.val + 1) := by
  constructor
  · by_contra hn
    have heq : clip (cumulative x i - s) = 1 := clip_eq_one (by linarith)
    have hle := clip_le_one (cumulative x (i.val + 1) - s)
    unfold slotMass at h
    rw [heq] at h
    linarith
  · by_contra hn
    have heq : clip (cumulative x (i.val + 1) - s) = 0 := clip_eq_zero (by linarith)
    have hge := clip_nonneg (cumulative x i - s)
    unfold slotMass at h
    rw [heq] at h
    linarith

/-- Sorting the cells implies the adjacent-slot comparison used in both
Shmoys--Tardos load estimates, including cells straddling a boundary. -/
theorem slotMass_adjacent {n : ℕ} (a x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (ha : Antitone a) (s : ℕ) (i j : Fin n)
    (hi : 0 < slotMass x s i) (hj : 0 < slotMass x (s + 1) j) : a j ≤ a i := by
  apply ha
  by_contra hn
  have hji : j.val + 1 ≤ i.val := by omega
  have hcumulative := cumulative_mono x hx hji
  have hleft := (slotMass_positive_bounds x s i hi).1
  have hright := (slotMass_positive_bounds x (s + 1) j hj).2
  push_cast at hright
  linarith


variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

/-- A concrete finite packing: all slots except the last are full; the last
may be empty. Adjacent support is ordered by decreasing owner value. -/
structure SlotPacking (a x : Agent → Cell → ℝ) where
  count : Agent → ℕ
  mass : (j : Agent) → Fin (count j + 1) → Cell → ℝ
  nonneg : ∀ j r e, 0 ≤ mass j r e
  column : ∀ j e, ∑ r, mass j r e = x j e
  row_le : ∀ j r, ∑ e, mass j r e ≤ 1
  full : ∀ j (r : Fin (count j)), ∑ e, mass j r.castSucc e = 1
  adjacent : ∀ j (r : Fin (count j)) e e',
    0 < mass j r.castSucc e → 0 < mass j r.succ e' → a j e' ≤ a j e

/-- Sorting by negative value, with the finite enumeration breaking ties. -/
def sortedOrder (a : Cell → ℝ) : Fin (Fintype.card Cell) ≃ Cell :=
  (Tuple.sort (fun i => -a ((Fintype.equivFin Cell).symm i))).trans
    (Fintype.equivFin Cell).symm

theorem sortedOrder_antitone (a : Cell → ℝ) : Antitone (a ∘ sortedOrder a) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -a ((Fintype.equivFin Cell).symm i)) hij
  change -a (sortedOrder a i) ≤ -a (sortedOrder a j) at h
  change a (sortedOrder a j) ≤ a (sortedOrder a i)
  linarith

/-- The actual consecutive sorted-slot construction. Its only hypothesis is
nonnegativity of the input fractional masses. No matching or load estimate is
included as an input. -/
def makePacking (a x : Agent → Cell → ℝ) (hx : ∀ j e, 0 ≤ x j e) : SlotPacking a x where
  count j := ⌊∑ e, x j e⌋₊
  mass j r e := slotMass (x j ∘ sortedOrder (a j)) r ((sortedOrder (a j)).symm e)
  nonneg j r e := slotMass_nonneg _ (fun i => hx j _) _ _
  column j e := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r => slotMass (x j ∘ sortedOrder (a j)) r ((sortedOrder (a j)).symm e))]
    have hN : (∑ i, (x j ∘ sortedOrder (a j)) i) ≤ (⌊∑ e, x j e⌋₊ + 1 : ℕ) := by
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp (sortedOrder (a j)) (x j)]
      exact le_of_lt (by exact_mod_cast Nat.lt_floor_add_one (∑ e, x j e))
    simpa using slotMass_column (x j ∘ sortedOrder (a j))
      (fun i => hx j _) (⌊∑ e, x j e⌋₊ + 1) hN ((sortedOrder (a j)).symm e)
  row_le j r := by
    rw [← Equiv.sum_comp (sortedOrder (a j))
      (fun e => slotMass (x j ∘ sortedOrder (a j)) r ((sortedOrder (a j)).symm e))]
    simp only [Equiv.symm_apply_apply]
    rw [slotMass_row]
    exact clip_le_one _
  full j r := by
    rw [← Equiv.sum_comp (sortedOrder (a j))
      (fun e => slotMass (x j ∘ sortedOrder (a j)) r.castSucc ((sortedOrder (a j)).symm e))]
    simp only [Equiv.symm_apply_apply]
    rw [slotMass_row]
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp (sortedOrder (a j)) (x j)]
    apply clip_eq_one
    have hr : (r.val : ℝ) + 1 ≤ ⌊∑ e, x j e⌋₊ := by exact_mod_cast r.isLt
    have hf := Nat.floor_le (show 0 ≤ ∑ e, x j e from Finset.sum_nonneg (fun e _ => hx j e))
    simp only [Fin.val_castSucc]
    linarith
  adjacent j r e e' he he' := by
    have h := slotMass_adjacent (a j ∘ sortedOrder (a j))
      (x j ∘ sortedOrder (a j)) (fun i => hx j _) (sortedOrder_antitone (a j))
      r ((sortedOrder (a j)).symm e) ((sortedOrder (a j)).symm e') he he'
    simpa using h

end EnvyFreeResearch.Full.UpperRounding
