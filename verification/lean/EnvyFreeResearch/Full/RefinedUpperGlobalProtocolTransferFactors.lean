import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import Mathlib

/-! Finite safe-factor selection used by the two-shrink transfer step.
A forbidden interval can contain at most one of the geometric factors. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
open scoped Classical

/-- With k choices and k rows, one diagonal row forbidding none and every
other row forbidding at most one choice leave a safe choice. -/
theorem safe_choice {k : ℕ} (bad : Fin k → Fin k → Prop) (j : Fin k)
    (hunique : ∀ i e f, bad i e → bad i f → e=f)
    (hdiag : ∀ e, ¬bad j e) : ∃ e, ∀ i, ¬bad i e := by
  by_contra! h
  choose row hrow using h
  have hinj : Function.Injective row := by
    intro e f he
    exact hunique (row e) e f (hrow e) (he ▸ hrow f)
  have hnot : j ∉ Set.range row := by
    rintro ⟨e,he⟩
    exact hdiag e (he ▸ hrow e)
  have hc := Fintype.card_lt_of_injective_of_notMem row hinj hnot
  omega

def factor (theta tau : ℝ) (e : ℕ) : ℝ := (2/theta)*(8/tau)^e

theorem factor_pos {theta tau : ℝ} (htheta : 0 < theta) (htau : 0 < tau) (e : ℕ) :
    0 < factor theta tau e := by unfold factor; positivity

theorem factor_separated {theta tau : ℝ} (htheta : 0 < theta)
    (htau : 0 < tau) (htau1 : tau ≤ 1) {e f : ℕ} (hef : e < f) :
    factor theta tau e * (8/tau) ≤ factor theta tau f := by
  have hb : 1 ≤ 8/tau := (le_div_iff₀ htau).mpr (by linarith)
  unfold factor
  rw [mul_assoc, ← pow_succ]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by omega)) (by positivity)

theorem forbidden_unique {theta tau x : ℝ} (htheta : 0 < theta)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hx : 0 ≤ x) {e f : ℕ}
    (he : 3*tau/8 < factor theta tau e*x ∧ factor theta tau e*x < 2)
    (hf : 3*tau/8 < factor theta tau f*x ∧ factor theta tau f*x < 2) : e=f := by
  have impossible (a b : ℕ) (hab : a < b)
      (ha : 3*tau/8 < factor theta tau a*x)
      (hb : factor theta tau b*x < 2) : False := by
    have hs := mul_le_mul_of_nonneg_right (factor_separated htheta htau htau1 hab) hx
    have hs' : (factor theta tau a*x)*8 ≤ (factor theta tau b*x)*tau := by
      apply (div_le_iff₀ htau).mp
      calc
        factor theta tau a*x*8/tau = factor theta tau a*(8/tau)*x := by ring
        _ ≤ _ := hs
    nlinarith
  rcases lt_trichotomy e f with h | h | h
  · exact False.elim (impossible e f h he.1 hf.2)
  · exact h
  · exact False.elim (impossible f e h hf.1 he.2)

theorem geometric_safe_factor {k : ℕ} (theta tau : ℝ) (x : Fin k → ℝ) (j : Fin k)
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hx : ∀ i, 0 ≤ x i) (hj : x j=0) :
    ∃ e : Fin k, ∀ i, factor theta tau e.val*x i ≤ 3*tau/8 ∨
      2 ≤ factor theta tau e.val*x i := by
  obtain ⟨e,he⟩ := safe_choice
    (fun i e : Fin k => 3*tau/8 < factor theta tau e.val*x i ∧ factor theta tau e.val*x i < 2) j
    (fun i e f h1 h2 => Fin.ext (forbidden_unique htheta htau htau1 (hx i) h1 h2))
    (by intro e; rw [hj]; simp; positivity)
  refine ⟨e,fun i => ?_⟩
  have hi := he i
  push_neg at hi
  by_cases hsmall : factor theta tau e.val*x i ≤ 3*tau/8
  · exact Or.inl hsmall
  · exact Or.inr (hi (lt_of_not_ge hsmall))

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
