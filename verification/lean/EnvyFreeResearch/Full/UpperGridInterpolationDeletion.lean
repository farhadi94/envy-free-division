import EnvyFreeResearch.Full.UpperGridSensitivity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-cell deletion and the finite grid deletion bound

Deleting one interior grid point replaces its two incident signed cell
masses by their sum. The interpolation error is the exact error of a convex
interpolant across that merged cell. All zero-denominator cases are included.
-/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity

/-- Exact error at the deleted point: the true first-cell increment is `a`,
and interpolation across the merged cell uses the fraction `theta`. -/
def mergeError (a b theta : ℝ) : ℝ := |a - theta * (a + b)|

theorem mergeError_nonneg (a b theta : ℝ) : 0 ≤ mergeError a b theta := abs_nonneg _

theorem mergeError_le (a b theta : ℝ) (htheta : 0 ≤ theta ∧ theta ≤ 1) :
    mergeError a b theta ≤ |a| + |b| := by
  have heq : a - theta * (a + b) = (1 - theta) * a - theta * b := by ring
  unfold mergeError
  rw [heq]
  calc
    |(1 - theta) * a - theta * b| ≤ |(1 - theta) * a| + |theta * b| := abs_sub _ _
    _ = (1 - theta) * |a| + theta * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr htheta.2), abs_of_nonneg htheta.1]
    _ ≤ |a| + |b| := by
      nlinarith [abs_nonneg a, abs_nonneg b, mul_nonneg htheta.1 (abs_nonneg a),
        mul_nonneg (sub_nonneg.mpr htheta.2) (abs_nonneg b)]

/-- The manuscript's cross multiplication, including vanishing variation
and vanishing merged denominator. -/
theorem normalized_error_le (e A rest merged : ℝ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hr : 0 ≤ rest) (hm : 0 ≤ merged) (hea : e ≤ A) :
    e / (rest + merged + e) ≤ A / (rest + A) := by
  by_cases hv : rest + A = 0
  · have hezero : e = 0 := by linarith
    simp [hezero, hv]
  · have hvpos : 0 < rest + A := lt_of_le_of_ne (add_nonneg hr hA) (Ne.symm hv)
    by_cases hd : rest + merged + e = 0
    · simp only [hd, div_zero]
      exact div_nonneg hA hvpos.le
    · have hdpos : 0 < rest + merged + e :=
        lt_of_le_of_ne (add_nonneg (add_nonneg hr hm) he) (Ne.symm hd)
      apply (div_le_div_iff₀ hdpos hvpos).mpr
      nlinarith [mul_le_mul_of_nonneg_right hea hr, mul_nonneg hA hm]

variable {Row Coord : Type*} [Fintype Coord]

def incident (x : Row → Coord → ℝ) (u v : Row) (left right : Coord) : ℝ :=
  |x u left - x v left| + |x u right - x v right|

def restVariation (x : Row → Coord → ℝ) (u v : Row) (left right : Coord) : ℝ :=
  ∑ a ∈ ({left, right} : Finset Coord)ᶜ, |x u a - x v a|

/-- Sum of absolute signed masses in the actual coarsened cell list: one
merged cell, and every nonincident cell unchanged. -/
def deletedVariation (x : Row → Coord → ℝ) (u v : Row) (left right : Coord) : ℝ :=
  restVariation x u v left right +
    |(x u left - x v left) + (x u right - x v right)|

theorem distance_eq_rest_add_incident (x : Row → Coord → ℝ) (u v : Row)
    (left right : Coord) (hne : left ≠ right) :
    distance x u v = restVariation x u v left right + incident x u v left right := by
  have h := Finset.sum_add_sum_compl ({left, right} : Finset Coord)
    (fun a => |x u a - x v a|)
  simpa [distance, restVariation, incident, hne, add_comm] using h.symm

theorem deletedVariation_eq (x : Row → Coord → ℝ) (u v : Row)
    (left right : Coord) (hne : left ≠ right) :
    deletedVariation x u v left right = distance x u v - incident x u v left right +
      |(x u left - x v left) + (x u right - x v right)| := by
  rw [distance_eq_rest_add_incident x u v left right hne]
  simp [deletedVariation]

def deletionError (x : Row → Coord → ℝ) (u v : Row) (left right : Coord) (theta : ℝ) : ℝ :=
  mergeError (x u left - x v left) (x u right - x v right) theta

def normalizedDeletion (x : Row → Coord → ℝ) (u v : Row) (left right : Coord)
    (theta : ℝ) : ℝ :=
  deletionError x u v left right theta /
    (deletedVariation x u v left right + deletionError x u v left right theta)

theorem normalizedDeletion_nonneg (x : Row → Coord → ℝ) (u v : Row)
    (left right : Coord) (theta : ℝ) : 0 ≤ normalizedDeletion x u v left right theta :=
  div_nonneg (mergeError_nonneg _ _ _) (add_nonneg
    (add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _))

theorem normalizedDeletion_le_incident (x : Row → Coord → ℝ) (u v : Row)
    (left right : Coord) (hne : left ≠ right) (theta : ℝ) (htheta : 0 ≤ theta ∧ theta ≤ 1) :
    normalizedDeletion x u v left right theta ≤ incident x u v left right / distance x u v := by
  rw [distance_eq_rest_add_incident x u v left right hne]
  exact normalized_error_le _ _ _ _ (mergeError_nonneg _ _ _)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _)
    (mergeError_le _ _ theta htheta)

variable [Fintype Row] [Nonempty Row]

def maxDeletion (x : Row → Coord → ℝ) (left right : Coord) (theta : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun uv : Row × Row => normalizedDeletion x uv.1 uv.2 left right theta)

theorem maxDeletion_nonneg (x : Row → Coord → ℝ) (left right : Coord) (theta : ℝ) :
    0 ≤ maxDeletion x left right theta := by
  obtain ⟨u⟩ := ‹Nonempty Row›
  exact (normalizedDeletion_nonneg x u u left right theta).trans
    (Finset.le_sup' (fun uv : Row × Row => normalizedDeletion x uv.1 uv.2 left right theta)
      (Finset.mem_univ (u, u)))

theorem maxDeletion_le_sensitivities (x : Row → Coord → ℝ) (left right : Coord)
    (hne : left ≠ right) (theta : ℝ) (htheta : 0 ≤ theta ∧ theta ≤ 1) :
    maxDeletion x left right theta ≤ sensitivity x left + sensitivity x right := by
  apply Finset.sup'_le
  intro uv _
  apply (normalizedDeletion_le_incident x uv.1 uv.2 left right hne theta htheta).trans
  rw [incident, add_div]
  exact add_le_add (ratio_le_sensitivity x left uv.1 uv.2) (ratio_le_sensitivity x right uv.1 uv.2)

/-- Each logical cell is incident to at most two interior deletion points.
The bound holds over any subset of those points. -/
theorem sum_deletion_le {m : ℕ} (x : Row → Fin (m + 1) → ℝ) (theta : Fin m → ℝ)
    (htheta : ∀ p, 0 ≤ theta p ∧ theta p ≤ 1) (points : Finset (Fin m)) :
    ∑ p ∈ points, maxDeletion x p.castSucc p.succ (theta p) ≤
      2 * ((Fintype.card Row : ℝ) - 1) := by
  have hleft : ∑ p : Fin m, sensitivity x p.castSucc ≤ ∑ a, sensitivity x a := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sensitivity_nonneg x _)
  have hright : ∑ p : Fin m, sensitivity x p.succ ≤ ∑ a, sensitivity x a := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sensitivity_nonneg x _)
  calc
    ∑ p ∈ points, maxDeletion x p.castSucc p.succ (theta p) ≤
        ∑ p : Fin m, maxDeletion x p.castSucc p.succ (theta p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ points)
        (fun p _ _ => maxDeletion_nonneg x _ _ _)
    _ ≤ ∑ p : Fin m, (sensitivity x p.castSucc + sensitivity x p.succ) := by
      apply Finset.sum_le_sum
      intro p _
      apply maxDeletion_le_sensitivities x _ _ _ (theta p) (htheta p)
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    _ = (∑ p : Fin m, sensitivity x p.castSucc) + ∑ p : Fin m, sensitivity x p.succ :=
      Finset.sum_add_distrib
    _ ≤ 2 * ∑ a, sensitivity x a := by linarith
    _ ≤ 2 * ((Fintype.card Row : ℝ) - 1) := mul_le_mul_of_nonneg_left (sum_sensitivity_le x) (by norm_num)

end EnvyFreeResearch.Full.UpperGridInterpolation
