import EnvyFreeResearch.Full.UpperGridInterpolationExpectation
import Mathlib.Logic.Equiv.Option

/-! Sorting commutes with deleting the actual corresponding raw coordinate. -/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity UpperSortedGrid

/-- Restrict a permutation after deleting one corresponding pair of indices. -/
theorem exists_delete_permutation {n : ℕ} (perm : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : perm i = j) :
    ∃ reduced : Equiv.Perm (Fin n), ∀ k,
      j.succAbove (reduced k) = perm (i.succAbove k) := by
  let e := (finSuccEquiv' i).symm.trans (perm.trans (finSuccEquiv' j))
  have hn : e none = none := by simp [e, hij]
  refine ⟨e.removeNone, ?_⟩
  intro k
  have hs : some (e.removeNone k) = e (some k) := by
    apply Equiv.removeNone_some
    cases h : e (some k) with
    | none => exact (Option.some_ne_none k (e.injective (h.trans hn.symm))).elim
    | some a => exact ⟨a, rfl⟩
  have h := congrArg (finSuccEquiv' j).symm hs
  simpa [e] using h

/-- This holds with repeated coordinates too: it deletes the occurrence
selected by the actual sorting permutation. -/
theorem sorted_removeNth {n : ℕ} (values : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    sorted (j.removeNth values) =
      ((select values).symm j).removeNth (sorted values) := by
  let i := (select values).symm j
  obtain ⟨reduced, hreduce⟩ := exists_delete_permutation (select values) i j (by simp [i])
  have heq : (j.removeNth values) ∘ reduced = i.removeNth (sorted values) := by
    funext k
    simp only [Function.comp_apply, Fin.removeNth, sorted]
    rw [hreduce]
  have hm : Monotone ((j.removeNth values) ∘ reduced) := by
    rw [heq]
    exact (sorted_monotone values).comp (Fin.strictMono_succAbove i).monotone
  have hu := Tuple.unique_monotone (f := j.removeNth values)
    (sorted_monotone (j.removeNth values)) hm
  exact hu.trans heq

variable {Row : Type*} [Fintype Row] [Nonempty Row]

theorem gridScore_unique_interior {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (p : Fin m)
    (hunique : ∀ j, sorted values j = sorted values p.succ.castSucc → j = p.succ.castSucc) :
    gridScore F L values (sorted values p.succ.castSucc) = gridDeletions F L values p := by
  rw [gridScore, fiberMean_unique _ _ _ hunique, nodeScores_interior]

/-- The original grid's row variation is the true coarsened variation of
the augmented grid after removing the corresponding inserted raw coordinate. -/
theorem original_variation_eq {m : ℕ} (F : Row → ℝ → ℝ)
    (values : Fin (m + 2) → ℝ) (raw : Fin (m + 2)) (p : Fin m)
    (hrank : (select values).symm raw = p.succ.castSucc) (u v : Row) :
    (∑ e : Fin m,
      |(F u (sorted (raw.removeNth values) e.succ) - F u (sorted (raw.removeNth values) e.castSucc)) -
       (F v (sorted (raw.removeNth values) e.succ) - F v (sorted (raw.removeNth values) e.castSucc))|) =
      deletedVariation (gridRows F values) u v p.castSucc p.succ := by
  rw [sorted_removeNth, hrank]
  exact delete_variation (fun i e => F i (sorted values e)) p u v

end EnvyFreeResearch.Full.UpperGridInterpolation
