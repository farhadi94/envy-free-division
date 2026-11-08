import EnvyFreeResearch.Full.MixedDensity
import EnvyFreeResearch.CoordinatedFamily

/-! Concrete signed-density states for the moving-frontier construction.
The update keeps one selected row exactly fixed and rebuilds every other row
with a negative cell followed by its compensating positive final tail. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedFrontier
open Set MixedDensity TranscriptAdversary CoordinatedFamily
open scoped Classical

structure State (Agent : Type*) (α : ℝ) where
  rows : Agent → Row
  frontier : ℝ
  nonnegative : 0 ≤ frontier
  proper : frontier < 1
  ceiling : ∀ i, TerminalCeiling (rows i).cumulative
  tail : Agent → ℝ
  tail_positive : ∀ i, 0 < tail i
  density_tail : ∀ i x, x ∈ Ioc frontier (1 : ℝ) → (rows i).density x = tail i
  prefix_coefficients : ∀ i j, i ≠ j → ∀ x ∈ Ioc (0 : ℝ) frontier,
    PairCoefficients α ((rows i).density x) ((rows j).density x)

def initial (Agent : Type*) (α : ℝ) : State Agent α where
  rows := fun _ => Row.cell 0 1 1
  frontier := 0
  nonnegative := le_rfl
  proper := by norm_num
  ceiling := by
    intro i
    constructor
    · norm_num [Row.cumulative_cell 0 1 1 1 (by norm_num) (by norm_num)]
    · intro x hx
      rw [Row.cumulative_cell 0 1 1 x (by norm_num) hx.1,
        min_eq_left hx.2.le, sub_zero, max_eq_left hx.1, one_mul]
      exact hx.2
  tail := fun _ => 1
  tail_positive := fun _ => by norm_num
  density_tail := by
    intro i x hx
    simp [Row.cell, hx]
  prefix_coefficients := by
    intro i j hij x hx
    exact False.elim (not_lt_of_ge hx.2 hx.1)

variable {Agent : Type*} {α : ℝ}

theorem distinguished_coefficients (hα : 0 < α) (j : Agent) (D : ℝ) (hD : 0 ≤ D)
    (i k : Agent) (hik : i ≠ k) :
    PairCoefficients α (if i = j then D else -((1 + α) / α) * D)
      (if k = j then D else -((1 + α) / α) * D) := by
  classical
  have hd : -((1 + α) / α) * D ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (by linarith) hα.le)) hD
  by_cases hij : i = j
  · have hkj : k ≠ j := by intro h; exact hik (hij.trans h.symm)
    simp only [ite_eq_left hij, ite_eq_right hkj]
    exact dominated_pair_coefficients hα hD le_rfl
  · by_cases hkj : k = j
    · simp only [ite_eq_right hij, ite_eq_left hkj]
      exact cell_condition_coefficients hα (Or.inr (Or.inr ⟨hD, le_rfl⟩))
    · simp only [ite_eq_right hij, ite_eq_right hkj]
      exact nonpositive_pair_coefficients hα.le hd hd

def advance (S : State Agent α) (hα : 0 < α) (j : Agent)
    (r : ℝ) (hlr : S.frontier < r) (hr : r < 1) : State Agent α := by
  classical
  let d : ℝ := -((1 + α) / α) * S.tail j
  have hd : d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg (by linarith) hα.le)) (S.tail_positive j).le
  let rows : Agent → Row := fun i =>
    if i = j then S.rows i else (S.rows i).rebuilt S.frontier r d
  let tail : Agent → ℝ := fun i => if i = j then S.tail i else
    (1 - ((S.rows i).cumulative S.frontier + d * (r - S.frontier))) / (1 - r)
  refine {
    rows := rows
    frontier := r
    nonnegative := S.nonnegative.trans hlr.le
    proper := hr
    ceiling := ?_
    tail := tail
    tail_positive := ?_
    density_tail := ?_
    prefix_coefficients := ?_ }
  · intro i
    by_cases hij : i = j
    · simpa [rows, hij] using S.ceiling i
    · simpa [rows, hij] using (S.rows i).rebuilt_terminal_ceiling
        (S.ceiling i) S.nonnegative hlr hr hd
  · intro i
    by_cases hij : i = j
    · simpa [tail, hij] using S.tail_positive i
    · simp only [tail, ite_eq_right hij]
      exact rebuild_tail_slope_positive
        ((S.ceiling i).2 S.frontier ⟨S.nonnegative, S.proper⟩) hlr.le hr hd
  · intro i x hx
    by_cases hij : i = j
    · simp only [rows, tail, ite_eq_left hij]
      exact S.density_tail i x ⟨hlr.trans hx.1, hx.2⟩
    · simp only [rows, tail, ite_eq_right hij]
      exact Row.rebuilt_density_tail (S.rows i) hx hlr.le
  · intro i k hik x hx
    by_cases hxl : x ≤ S.frontier
    · have heq : ∀ a, (rows a).density x = (S.rows a).density x := by
        intro a
        by_cases haj : a = j
        · simp [rows, haj]
        · simp only [rows, ite_eq_right haj]
          exact Row.rebuilt_density_prefix (S.rows a) ⟨hx.1, hxl⟩ hlr.le
      rw [heq i, heq k]
      exact S.prefix_coefficients i k hik x ⟨hx.1, hxl⟩
    · have heq : ∀ a, (rows a).density x = if a = j then S.tail j else d := by
        intro a
        by_cases haj : a = j
        · subst a
          simp only [rows, ite_true]
          exact S.density_tail j x ⟨lt_of_not_ge hxl, hx.2.trans hr.le⟩
        · simp only [rows, ite_eq_right haj]
          exact Row.rebuilt_density_cell (S.rows a) ⟨lt_of_not_ge hxl, hx.2⟩
      rw [heq i, heq k]
      exact distinguished_coefficients hα j (S.tail j) (S.tail_positive j).le i k hik

@[simp] theorem advance_frontier (S : State Agent α) (hα : 0 < α)
    (j : Agent) (r : ℝ) (hlr : S.frontier < r) (hr : r < 1) :
    (advance S hα j r hlr hr).frontier = r := rfl

/-- The currently queried row is kept exactly, not merely at finitely many roots. -/
@[simp] theorem advance_fixed_row (S : State Agent α) (hα : 0 < α)
    (j : Agent) (r : ℝ) (hlr : S.frontier < r) (hr : r < 1) :
    (advance S hα j r hlr hr).rows j = S.rows j := by
  simp [advance]

theorem advance_prefix (S : State Agent α) (hα : 0 < α)
    (j : Agent) (r : ℝ) (hlr : S.frontier < r) (hr : r < 1)
    (i : Agent) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) S.frontier) :
    ((advance S hα j r hlr hr).rows i).cumulative x = (S.rows i).cumulative x := by
  classical
  by_cases hij : i = j
  · subst i
    rw [advance_fixed_row]
  · change (if i = j then S.rows i else
        (S.rows i).rebuilt S.frontier r (-((1 + α) / α) * S.tail j)).cumulative x = _
    rw [ite_eq_right hij, Row.cumulative_rebuilt (S.rows i) S.frontier r _ x
      S.nonnegative hlr hr ⟨hx.1, hx.2.trans S.proper.le⟩, rebuild_prefix hx.2]

end EnvyFreeResearch.Full.MixedFrontier
