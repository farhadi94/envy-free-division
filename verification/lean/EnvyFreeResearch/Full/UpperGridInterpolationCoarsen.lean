import EnvyFreeResearch.Full.UpperGridInterpolationDeletion

/-! Deletion of an actual cumulative-grid coordinate and its cell variation. -/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity

variable {Row : Type*} {m : ℕ}

def increments (F : Row → Fin (m + 2) → ℝ) : Row → Fin (m + 1) → ℝ :=
  fun i e => F i e.succ - F i e.castSucc

/-- Delete the interior coordinate numbered `p+1`. -/
def deletePoint (F : Row → Fin (m + 2) → ℝ) (p : Fin m) : Row → Fin (m + 1) → ℝ :=
  fun i e => F i (p.succ.castSucc.succAbove e)

theorem delete_increments (F : Row → Fin (m + 2) → ℝ) (p e : Fin m) (i : Row) :
    deletePoint F p i e.succ - deletePoint F p i e.castSucc =
      if e = p then increments F i p.castSucc + increments F i p.succ
      else increments F i (p.succ.succAbove e) := by
  simp only [deletePoint, increments, Fin.succAbove, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ, Nat.lt_add_one_iff]
  by_cases he : e = p
  · subst e
    simp
  · by_cases hlt : e < p
    · have hle : e ≤ p := hlt.le
      simp only [he, Fin.lt_def, Fin.le_def] at hlt hle ⊢
      simp [hlt, hle, Fin.castSucc_succ]
    · have hle : ¬e ≤ p := by exact fun h => he (le_antisymm h (le_of_not_gt hlt))
      simp only [Fin.lt_def, Fin.le_def] at hlt hle
      simp [he, hlt, hle, Fin.castSucc_succ]

/-- Coarsening removes precisely two old variation summands and adds their
merged signed increment. This is proved for the actual deleted tuple. -/
theorem delete_variation (F : Row → Fin (m + 2) → ℝ) (p : Fin m) (u v : Row) :
    (∑ e : Fin m, |(deletePoint F p u e.succ - deletePoint F p u e.castSucc) -
      (deletePoint F p v e.succ - deletePoint F p v e.castSucc)|) =
      deletedVariation (increments F) u v p.castSucc p.succ := by
  let x := increments F
  let old (e : Fin m) := |x u (p.succ.succAbove e) - x v (p.succ.succAbove e)|
  let new (e : Fin m) := |(deletePoint F p u e.succ - deletePoint F p u e.castSucc) -
      (deletePoint F p v e.succ - deletePoint F p v e.castSucc)|
  have hrest : ∑ e ∈ Finset.univ.erase p, new e = ∑ e ∈ Finset.univ.erase p, old e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [new, old, x, delete_increments, (Finset.mem_erase.mp he).1]
  have hold := Finset.sum_erase_add Finset.univ old (Finset.mem_univ p)
  have hnew := Finset.sum_erase_add Finset.univ new (Finset.mem_univ p)
  rw [hrest] at hnew
  have hdist := Fin.sum_univ_succAbove
    (fun e => |x u e - x v e|) p.succ
  have hpold : old p = |x u p.castSucc - x v p.castSucc| := by simp [old]
  have hpnew : new p = |(x u p.castSucc - x v p.castSucc) + (x u p.succ - x v p.succ)| := by
    simp only [new, delete_increments]
    congr 1
    dsimp [x]
    ring
  have hne : p.castSucc ≠ p.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rw [deletedVariation_eq _ _ _ _ _ hne]
  change (∑ e, new e) = distance x u v - incident x u v p.castSucc p.succ + _
  change distance x u v = _ at hdist
  rw [hpold] at hold
  rw [hpnew] at hnew
  dsimp only [incident]
  linarith

/-- The two incident signed increments give exactly the cumulative error
of the convex interpolation across the deleted point. -/
theorem deletionError_eq_cumulative (F : Row → Fin (m + 2) → ℝ) (p : Fin m)
    (u v : Row) (theta : ℝ) :
    deletionError (increments F) u v p.castSucc p.succ theta =
      |(F u p.castSucc.succ - F v p.castSucc.succ) -
        ((1 - theta) * (F u p.castSucc.castSucc - F v p.castSucc.castSucc) +
          theta * (F u p.succ.succ - F v p.succ.succ))| := by
  unfold deletionError mergeError increments
  simp only [Fin.castSucc_succ]
  congr 1
  ring

end EnvyFreeResearch.Full.UpperGridInterpolation
