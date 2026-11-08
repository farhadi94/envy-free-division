import EnvyFreeResearch.Full.UpperSnapshotSmallLaws

/-! Concrete cumulative targets for zero-disagreement equal partitions and
for the second stage of a positive small-disagreement candidate. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCorrectionExecution
variable {J : ℕ}

def equalTargets (J : ℕ) (j : Fin (J + 1)) : I := amount (j.val : ℝ) J

def remainderTargets (J : ℕ) (t : ℝ) (j : Fin (J + 1)) : I :=
  if j.val < J then amount (j.val * t) (1 - t) else 1

theorem equalTargets_value (hJ : 0 < J) (j : Fin (J + 1)) :
    (equalTargets J j : ℝ) = j.val / J := by
  unfold equalTargets
  rw [amount_eq_fraction _ _ (by positivity) (by exact_mod_cast Nat.le_of_lt_succ j.isLt)
    (by exact_mod_cast hJ)]
  rfl

theorem equalTargets_zero (hJ : 0 < J) : equalTargets J 0 = 0 := by
  apply Subtype.ext
  simpa using equalTargets_value hJ (0 : Fin (J + 1))

theorem equalTargets_last (hJ : 0 < J) : equalTargets J (Fin.last J) = 1 := by
  apply Subtype.ext
  rw [equalTargets_value hJ]
  change (J : ℝ) / J = 1
  exact div_self (by exact_mod_cast Nat.ne_of_gt hJ)

theorem equalTargets_strict (hJ : 0 < J) : StrictMono (equalTargets J) := by
  intro i j hij
  change (equalTargets J i : ℝ) < equalTargets J j
  rw [equalTargets_value hJ, equalTargets_value hJ]
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < J by exact_mod_cast hJ)).mpr
  exact_mod_cast hij

theorem equalTargets_increment (hJ : 0 < J) (j : Fin J) :
    (equalTargets J j.succ : ℝ) - equalTargets J j.castSucc = 1 / J := by
  rw [equalTargets_value hJ, equalTargets_value hJ]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem remainder_target_lt (_hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1)
    (j : Fin (J + 1)) (hj : j.val < J) : (j.val : ℝ) * t < 1 - t := by
  have hsucc : (j.val : ℝ) + 1 ≤ J := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_right hsucc ht.le
  linarith

theorem remainderTargets_value (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1)
    (j : Fin (J + 1)) (hj : j.val < J) :
    (remainderTargets J t j : ℝ) = j.val * t / (1 - t) := by
  have hlt := remainder_target_lt hJ t ht hfit j hj
  have hden : 0 < 1 - t := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ j.val * t) hlt
  simp only [remainderTargets, hj, ite_true]
  rw [amount_eq_fraction _ _ (by positivity) hlt.le hden]
  rfl

theorem remainderTargets_zero (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1) :
    remainderTargets J t 0 = 0 := by
  apply Subtype.ext
  simpa using remainderTargets_value hJ t ht hfit (0 : Fin (J + 1)) hJ

theorem remainderTargets_last (t : ℝ) : remainderTargets J t (Fin.last J) = 1 := by
  simp [remainderTargets]

theorem remainderTargets_strict (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1) :
    StrictMono (remainderTargets J t) := by
  have ht1 : t < 1 := by
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  intro i j hij
  have hi : i.val < J := by have hh := j.isLt; change i.val < j.val at hij; omega
  change (remainderTargets J t i : ℝ) < remainderTargets J t j
  rw [remainderTargets_value hJ t ht hfit i hi]
  by_cases hj : j.val < J
  · rw [remainderTargets_value hJ t ht hfit j hj]
    apply (div_lt_div_iff_of_pos_right (sub_pos.mpr ht1)).mpr
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) ht
  · have hjlast : j = Fin.last J := by apply Fin.ext; have hh := j.isLt; simp only [Fin.val_last]; omega
    rw [hjlast, remainderTargets_last]
    exact (div_lt_one (sub_pos.mpr ht1)).mpr (remainder_target_lt hJ t ht hfit i hi)

theorem remainderTargets_increment (hJ : 0 < J) (t : ℝ) (ht : 0 < t) (hfit : (J : ℝ) * t < 1)
    (j : Fin J) (hj : j.val + 1 < J) :
    (remainderTargets J t j.succ : ℝ) - remainderTargets J t j.castSucc = t / (1 - t) := by
  rw [remainderTargets_value hJ t ht hfit _ hj, remainderTargets_value hJ t ht hfit _ j.isLt]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem remainderTargets_final_increment (hJ : 0 < J) (t : ℝ) (ht : 0 < t)
    (hfit : (J : ℝ) * t < 1) (j : Fin J) (hj : j.val + 1 = J) :
    (remainderTargets J t j.succ : ℝ) - remainderTargets J t j.castSucc =
      (1 - J * t) / (1 - t) := by
  have hs : j.succ = Fin.last J := by apply Fin.ext; exact hj
  rw [hs, remainderTargets_last, remainderTargets_value hJ t ht hfit _ j.isLt]
  have ht1 : t < 1 := by
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have he : (j.val : ℝ) + 1 = J := by exact_mod_cast hj
  change 1 - (j.val : ℝ) * t / (1 - t) = (1 - J * t) / (1 - t)
  field_simp
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotSmall
