import EnvyFreeResearch.Full.UpperGridInterpolationLinear
import EnvyFreeResearch.Full.UpperGridInterpolationRawDelete

/-! Identification with the original-grid cumulative interpolant. -/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity UpperSortedGrid

variable {Row : Type*} [Fintype Row] [Nonempty Row]

def FlatCompatible (F : Row → ℝ → ℝ) (L : ℝ → ℝ) : Prop :=
  ∀ i a b, a ≤ b → L a = L b → F i a = F i b

theorem remove_left {m : ℕ} (g : Fin (m + 2) → ℝ) (p : Fin m) :
    (p.succ.castSucc.removeNth g) p.castSucc = g p.castSucc.castSucc := by
  simp only [Fin.removeNth, Fin.succAbove]
  rw [ite_eq_left (show p.castSucc.castSucc < p.succ.castSucc from by simp [Fin.lt_def])]

theorem remove_right {m : ℕ} (g : Fin (m + 2) → ℝ) (p : Fin m) :
    (p.succ.castSucc.removeNth g) p.succ = g p.succ.succ := by
  simp only [Fin.removeNth, Fin.succAbove, lt_self_iff_false, ite_false]

/-- The symmetric score at a unique interior coordinate is precisely the
maximum normalized error for the original grid obtained by deleting it. -/
theorem gridScore_eq_linear {m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (hflat : FlatCompatible F L) (values : Fin (m + 2) → ℝ) (raw : Fin (m + 2))
    (p : Fin m) (hrank : (select values).symm raw = p.succ.castSucc)
    (hunique : ∀ j, values j = values raw → j = raw) :
    gridScore F L values (values raw) =
      linearMaximum F L (sorted (raw.removeNth values)) (values raw) := by
  let cuts := sorted (raw.removeNth values)
  let theta := gridTheta L values p
  have htest : sorted values p.succ.castSucc = values raw := by
    rw [← hrank]
    simp [sorted]
  have hleft : cuts p.castSucc = sorted values p.castSucc.castSucc := by
    dsimp only [cuts]
    rw [sorted_removeNth, hrank, remove_left]
  have hright : cuts p.succ = sorted values p.succ.succ := by
    dsimp only [cuts]
    rw [sorted_removeNth, hrank, remove_right]
  have hbetween : cuts p.castSucc ≤ values raw ∧ values raw ≤ cuts p.succ := by
    rw [hleft, hright, ← htest]
    exact ⟨sorted_monotone values (by simp [Fin.le_def]), sorted_monotone values (by simp [Fin.le_def])⟩
  have hlocal (i : Row) : linearEstimate (F i) L cuts (values raw) =
      (1 - theta) * F i (sorted values p.castSucc.castSucc) + theta * F i (sorted values p.succ.succ) := by
    have h := linearEstimate_local (F i) L cuts (sorted_monotone _) (fun e he =>
      (hflat i _ _ (sorted_monotone _ (by simp [Fin.le_def])) he.symm).symm)
      (values raw) p hbetween.1 hbetween.2
    simpa only [hleft, hright, ← htest, theta, gridTheta] using h
  have herr (u v : Row) : linearError F L cuts (values raw) u v =
      deletionError (gridRows F values) u v p.castSucc p.succ theta := by
    rw [linearError, hlocal, hlocal, ← htest]
    rw [gridRows, deletionError_eq_cumulative]
    simp only [Fin.castSucc_succ]
    congr 1
    ring
  have hvar (u v : Row) : distance (linearRows F cuts) u v =
      deletedVariation (gridRows F values) u v p.castSucc p.succ :=
    original_variation_eq F values raw p hrank u v
  have hu : ∀ j, sorted values j = sorted values p.succ.castSucc → j = p.succ.castSucc := by
    intro j hj
    have he : select values j = raw := hunique _ (hj.trans htest)
    exact ((select values).eq_symm_apply.mpr he).trans hrank
  rw [← htest, gridScore_unique_interior F L values p hu]
  change maxDeletion (gridRows F values) p.castSucc p.succ theta = linearMaximum F L cuts (sorted values p.succ.castSucc)
  rw [htest]
  unfold maxDeletion linearMaximum
  congr 1
  funext uv
  rw [herr, hvar]
  rfl

/-- The newly inserted test point has the ordinary original-grid error
whenever it is interior and distinct from the old finite grid. -/
theorem interpolationKernel_eq_linear {b m : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ)
    (hflat : FlatCompatible F L) (permanent : Fin b → ℝ) (samples : Fin m → ℝ)
    (test : ℝ) (htest : 0 < test ∧ test < 1)
    (hnew : ∀ j, augmented permanent samples j ≠ test) :
    interpolationKernel F L permanent samples test =
      linearMaximum F L (sorted (augmented permanent samples)) test := by
  obtain ⟨p, hp⟩ := augmented_test_interior permanent samples test htest
  have hu := augmented_test_unique permanent samples test hnew
  have h := gridScore_eq_linear F L hflat (augmented permanent (Fin.cons test samples))
    (sampleLabel (b := b) (0 : Fin (m + 1))) p hp (by
      intro j hj
      exact hu j (by simpa only [augmented_sample, Fin.cons_zero] using hj))
  simpa only [interpolationKernel, sampleScore, augmented_sample, Fin.cons_zero, augmented_remove_test] using h

end EnvyFreeResearch.Full.UpperGridInterpolation
