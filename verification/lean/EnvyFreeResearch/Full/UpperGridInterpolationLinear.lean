import EnvyFreeResearch.Full.UpperGridInterpolationSortDelete

/-! Cumulative interpolation on the original grid as an explicit cell sum. -/

noncomputable section

open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity UpperSortedGrid

theorem partial_increments {n : ℕ} (F : Fin (n + 1) → ℝ) (p : Fin n) :
    (∑ e : Fin n, if e < p then F e.succ - F e.castSucc else 0) = F p.castSucc - F 0 := by
  induction n with
  | zero => exact Fin.elim0 p
  | succ n ih =>
    refine Fin.cases ?_ (fun q => ?_) p
    · simp
    · rw [Fin.sum_univ_succ]
      have ht := ih (fun i => F i.succ) q
      have hzero : (0 : Fin (n + 1)) < q.succ := by simp [Fin.lt_def]
      simp only [hzero, ite_eq_left, Fin.succ_lt_succ_iff, Fin.castSucc_succ]
      rw [ht]
      simp

theorem weighted_increments_local {n : ℕ} (F : Fin (n + 1) → ℝ) (w : Fin n → ℝ)
    (p : Fin n) (theta : ℝ)
    (hbefore : ∀ e, e < p → (F e.succ - F e.castSucc) * w e = F e.succ - F e.castSucc)
    (hat : w p = theta)
    (hafter : ∀ e, p < e → (F e.succ - F e.castSucc) * w e = 0) :
    (∑ e, (F e.succ - F e.castSucc) * w e) =
      F p.castSucc - F 0 + theta * (F p.succ - F p.castSucc) := by
  have he (e : Fin n) : (F e.succ - F e.castSucc) * w e =
      (if e < p then F e.succ - F e.castSucc else 0) +
        (if e = p then theta * (F p.succ - F p.castSucc) else 0) := by
    rcases lt_trichotomy e p with h | rfl | h
    · simp [h, h.ne, hbefore e h]
    · simp [hat, mul_comm]
    · simp [h.not_gt, h.ne.symm, hafter e h]
  simp_rw [he]
  rw [Finset.sum_add_distrib, partial_increments]
  simp

def cellFraction {n : ℕ} (L : ℝ → ℝ) (cuts : Fin (n + 1) → ℝ) (z : ℝ) (e : Fin n) : ℝ :=
  (L (min (cuts e.succ) z) - L (min (cuts e.castSucc) z)) /
    (L (cuts e.succ) - L (cuts e.castSucc))

def linearEstimate {n : ℕ} (F L : ℝ → ℝ) (cuts : Fin (n + 1) → ℝ) (z : ℝ) : ℝ :=
  F (cuts 0) + ∑ e : Fin n, (F (cuts e.succ) - F (cuts e.castSucc)) * cellFraction L cuts z e

/-- A completed zero-volume cell has zero signed increment. This local
condition suffices, without absolute continuity of the underlying measures. -/
theorem linearEstimate_local {n : ℕ} (F L : ℝ → ℝ) (cuts : Fin (n + 1) → ℝ)
    (hcuts : Monotone cuts)
    (hflat : ∀ e : Fin n, L (cuts e.succ) = L (cuts e.castSucc) → F (cuts e.succ) = F (cuts e.castSucc))
    (z : ℝ) (p : Fin n) (hleft : cuts p.castSucc ≤ z) (hright : z ≤ cuts p.succ) :
    linearEstimate F L cuts z =
      (1 - (L z - L (cuts p.castSucc)) / (L (cuts p.succ) - L (cuts p.castSucc))) * F (cuts p.castSucc) +
      ((L z - L (cuts p.castSucc)) / (L (cuts p.succ) - L (cuts p.castSucc))) * F (cuts p.succ) := by
  have hsum := weighted_increments_local (fun e => F (cuts e)) (cellFraction L cuts z) p
    ((L z - L (cuts p.castSucc)) / (L (cuts p.succ) - L (cuts p.castSucc)))
  have hbefore (e : Fin n) (he : e < p) :
      (F (cuts e.succ) - F (cuts e.castSucc)) * cellFraction L cuts z e =
        F (cuts e.succ) - F (cuts e.castSucc) := by
    have hupper : cuts e.succ ≤ z := (hcuts (show e.succ ≤ p.castSucc from by change e.val + 1 ≤ p.val; exact he)).trans hleft
    have hlower : cuts e.castSucc ≤ z := (hcuts (show e.castSucc ≤ e.succ from by simp [Fin.le_def])).trans hupper
    simp only [cellFraction, min_eq_left hupper, min_eq_left hlower]
    by_cases hz : L (cuts e.succ) = L (cuts e.castSucc)
    · simp [hflat e hz]
    · rw [div_self (sub_ne_zero.mpr hz), mul_one]
  have hat : cellFraction L cuts z p =
      (L z - L (cuts p.castSucc)) / (L (cuts p.succ) - L (cuts p.castSucc)) := by
    simp only [cellFraction, min_eq_right hright, min_eq_left hleft]
  have hafter (e : Fin n) (he : p < e) :
      (F (cuts e.succ) - F (cuts e.castSucc)) * cellFraction L cuts z e = 0 := by
    have hlower : z ≤ cuts e.castSucc := hright.trans (hcuts (show p.succ ≤ e.castSucc from by change p.val + 1 ≤ e.val; exact he))
    have hupper : z ≤ cuts e.succ := hlower.trans (hcuts (show e.castSucc ≤ e.succ from by simp [Fin.le_def]))
    simp [cellFraction, min_eq_right hlower, min_eq_right hupper]
  rw [linearEstimate, hsum hbefore hat hafter]
  ring

variable {Row : Type*} [Fintype Row] [Nonempty Row]

def linearRows {n : ℕ} (F : Row → ℝ → ℝ) (cuts : Fin (n + 1) → ℝ) : Row → Fin n → ℝ :=
  fun i e => F i (cuts e.succ) - F i (cuts e.castSucc)

def linearError {n : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (cuts : Fin (n + 1) → ℝ)
    (z : ℝ) (i j : Row) : ℝ :=
  |(F i z - F j z) - (linearEstimate (F i) L cuts z - linearEstimate (F j) L cuts z)|

def linearMaximum {n : ℕ} (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (cuts : Fin (n + 1) → ℝ) (z : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Row × Row =>
    linearError F L cuts z ij.1 ij.2 /
      (distance (linearRows F cuts) ij.1 ij.2 + linearError F L cuts z ij.1 ij.2))

end EnvyFreeResearch.Full.UpperGridInterpolation
