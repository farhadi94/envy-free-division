import EnvyFreeResearch.Full.UpperGridInterpolationSortDelete

/-! Removing the distinguished fresh sample restores the original raw grid. -/

noncomputable section

open scoped Classical

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperSortedGrid

variable {b m : ℕ}

theorem augmented_remove_test (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (test : ℝ) :
    (sampleLabel (b := b) (0 : Fin (m + 1))).removeNth
      (augmented permanent (Fin.cons test samples)) = augmented permanent samples := by
  funext k
  simp only [Fin.removeNth]
  refine Fin.cases ?_ (fun q => ?_) k
  · have hind : (sampleLabel (b := b) (0 : Fin (m + 1))).succAbove 0 = 0 := by
      apply Fin.ext
      dsimp only [Fin.succAbove]
      split_ifs <;> simp_all [sampleLabel, Fin.lt_def] <;> omega
    rw [hind]
    simp [augmented]
  · refine Fin.lastCases ?_ (fun q => ?_) q
    · have hind : (sampleLabel (b := b) (0 : Fin (m + 1))).succAbove (Fin.last (b + m)).succ =
          (Fin.last (b + (m + 1))).succ := by
        apply Fin.ext
        dsimp only [Fin.succAbove]
        split_ifs <;> simp_all [sampleLabel, Fin.lt_def] <;> omega
      simpa [augmented] using
        congrArg (augmented permanent (Fin.cons test samples)) hind
    · refine Fin.addCases ?_ ?_ q
      · intro p
        have hind : (sampleLabel (b := b) (0 : Fin (m + 1))).succAbove (Fin.castAdd m p).castSucc.succ =
            (Fin.castAdd (m + 1) p).castSucc.succ := by
          apply Fin.ext
          dsimp only [Fin.succAbove]
          split_ifs <;> simp_all [sampleLabel, Fin.lt_def] <;> omega
        rw [hind]
        simp only [augmented, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_left]
      · intro p
        have hind : (sampleLabel (b := b) (0 : Fin (m + 1))).succAbove (sampleLabel (b := b) p) =
            sampleLabel (b := b) p.succ := by
          apply Fin.ext
          dsimp only [Fin.succAbove]
          split_ifs <;> simp_all [sampleLabel, Fin.lt_def] <;> omega
        change augmented permanent (Fin.cons test samples)
            ((sampleLabel (b := b) (0 : Fin (m + 1))).succAbove (sampleLabel p)) = _
        rw [hind, augmented_sample]
        simp only [Fin.cons_succ]
        exact (augmented_sample permanent samples p).symm

theorem augmented_test_unique (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (test : ℝ)
    (hnew : ∀ j, augmented permanent samples j ≠ test) :
    ∀ j, augmented permanent (Fin.cons test samples) j = test →
      j = sampleLabel (b := b) (0 : Fin (m + 1)) := by
  intro j hj
  rcases Fin.eq_self_or_eq_succAbove (sampleLabel (b := b) (0 : Fin (m + 1))) j with h | ⟨i, rfl⟩
  · exact h
  · have he := congrFun (augmented_remove_test permanent samples test) i
    exact (hnew i (he.symm.trans hj)).elim

/-- A fresh interior test point occupies a genuine interior position in the
sorted augmented grid, regardless of coincidences among the old boundaries. -/
theorem augmented_test_interior (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (test : ℝ)
    (htest : 0 < test ∧ test < 1) :
    ∃ p : Fin (b + (m + 1)),
      (select (augmented permanent (Fin.cons test samples))).symm (sampleLabel (b := b) (0 : Fin (m + 1))) =
        p.succ.castSucc := by
  let values := augmented permanent (Fin.cons test samples)
  let rank := (select values).symm (sampleLabel (b := b) (0 : Fin (m + 1)))
  have hrank : sorted values rank = test := by simp [values, rank, sorted]
  have hzero : values 0 = 0 := by simp [values, augmented]
  have hone : values (Fin.last (b + (m + 1) + 1)) = 1 := by simp [values, augmented]
  obtain ⟨z, hz⟩ := sorted_contains values 0
  obtain ⟨o, ho⟩ := sorted_contains values (Fin.last (b + (m + 1) + 1))
  have hlo : 0 < rank.val := by
    by_contra hn
    have he : rank = 0 := Fin.ext (by change rank.val = 0; omega)
    have hm := sorted_monotone values (Fin.zero_le z)
    rw [← he, hrank, hz, hzero] at hm
    linarith [htest.1]
  have hhi : rank.val < b + (m + 1) + 1 := by
    by_contra hn
    have he : rank = Fin.last (b + (m + 1) + 1) := Fin.ext (by have := rank.isLt; simp; omega)
    have hm := sorted_monotone values (Fin.le_last o)
    rw [← he, hrank, ho, hone] at hm
    linarith [htest.2]
  refine ⟨⟨rank.val - 1, by omega⟩, ?_⟩
  change rank = _
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_succ]
  omega

end EnvyFreeResearch.Full.UpperGridInterpolation
