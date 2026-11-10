import Mathlib

/-! Scalar conclusions of the moat argument. These are explicitly ledger
lemmas, not substitutes for the concrete protocol lower-bound theorem. -/
namespace EnvyFreeResearch.Full.MoatLedger
open Filter
open scoped Topology

/-- Pass to the sharp moat width from strictly wider moats. -/
theorem right_limit {a b c p : ℝ} (ha : a < 1)
    (h : ∀ w, a < w → w < 1 → p ≤ b+c*w) : p ≤ b+c*a := by
  let w : ℕ → ℝ := fun m => a+(1-a)/((m:ℝ)+2)
  have hw0 (m : ℕ) : a < w m := by
    dsimp [w]
    have hpos : 0 < (1-a)/((m:ℝ)+2) := div_pos (by linarith) (by positivity)
    linarith
  have hw1 (m : ℕ) : w m < 1 := by
    dsimp [w]
    have hden : (1:ℝ) < (m:ℝ)+2 := by have hm := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
    have hdiv : (1-a)/((m:ℝ)+2) < 1-a :=
      (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hz : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0) :=
    by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hw : Tendsto w atTop (𝓝 a) := by
    have ht : Tendsto (fun m : ℕ => a+(1-a)*(1/((m:ℝ)+2))) atTop (𝓝 (a+(1-a)*0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
    simpa only [w, mul_zero, add_zero, div_eq_mul_inv, one_mul] using ht
  have hout : Tendsto (fun m => b+c*w m) atTop (𝓝 (b+c*a)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hw)
  exact ge_of_tendsto hout (Filter.Eventually.of_forall (fun m => h (w m) (hw0 m) (hw1 m)))

theorem one_row_bound {n p s q j : ℝ} (hn : 2 ≤ n) (hs : s ≤ 1) (hj : j ≤ 1-s)
    (h : p ≤ s/n + (2/n^2)*(q+j)) : n*(n*p-1)/2 ≤ q := by
  have hn0 : 0 < n := by linarith
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  have heq : n^2*(s/n+(2/n^2)*(q+j)) = n*s+2*(q+j) := by field_simp <;> ring
  rw [heq] at hm
  have hpos := mul_nonneg (show 0 ≤ n-2 by linarith) (show 0 ≤ 1-s by linarith)
  nlinarith

theorem two_row_answered_bound {n p q j : ℝ} (hn : 0 < n) (hj : j ≤ 1)
    (h : p ≤ (4/n^2)*(q+j)) : n^2*p/4-1 ≤ q := by
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  have heq : n^2*((4/n^2)*(q+j))=4*(q+j) := by field_simp <;> ring
  rw [heq] at hm
  nlinarith

theorem two_row_attempted_bound {n p q : ℝ} (hn : 0 < n)
    (h : p ≤ (4/n^2)*q) : n^2*p/4 ≤ q := by
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  have heq : n^2*((4/n^2)*q)=4*q := by field_simp <;> ring
  rw [heq] at hm
  nlinarith

/-- A uniform bound for every strictly wider moat yields the exact endpoint
coefficient without ever admitting equal-arc decoder exceptions. -/
theorem one_row_limit {n p s q j : ℝ} (hn : 2 ≤ n)
    (h : ∀ w, 1/n < w → w < 1 → p ≤ s/n+(2*w/n)*(q+j)) :
    p ≤ s/n+(2/n^2)*(q+j) := by
  have hn0 : 0 < n := by linarith
  have ha : 1/n < 1 := (div_lt_one hn0).mpr (by linarith)
  have ht := right_limit (b := s/n) (c := 2*(q+j)/n) ha (by
    intro w hw hw1
    have hh := h w hw hw1
    convert hh using 1 <;> ring)
  convert ht using 1 <;> field_simp <;> ring

theorem two_row_limit {n p q j : ℝ} (hn : 2 ≤ n)
    (h : ∀ w, 1/n < w → w < 1 → p ≤ (4*w/n)*(q+j)) :
    p ≤ (4/n^2)*(q+j) := by
  have hn0 : 0 < n := by linarith
  have ha : 1/n < 1 := (div_lt_one hn0).mpr (by linarith)
  have ht := right_limit (b := 0) (c := 4*(q+j)/n) ha (by
    intro w hw hw1
    have hh := h w hw hw1
    convert hh using 1 <;> ring)
  convert ht using 1 <;> field_simp <;> ring

/-- Eliminate the capped success probability before choosing the cutoff;
its value may depend on the cutoff and on the moat width. -/
theorem one_row_eliminate {n s q w : ℝ} (hn : 2 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hw : 1/n ≤ w) :
    s/n+(2*w/n)*(q+1-s) ≤ 1/n+(2*w/n)*q+2*(w-1/n)/n := by
  have hn0 : 0 < n := by linarith
  have hwn : 1 ≤ w*n := (div_le_iff₀ hn0).mp hw
  have hpos1 := mul_nonneg (show 0 ≤ n-2 by linarith) (show 0 ≤ 1-s by linarith)
  have hpos2 := mul_nonneg (show 0 ≤ w*n-1 by linarith) hs0
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn0)).mp
  have hleft : n^2*(s/n+(2*w/n)*(q+1-s)) = n*s+2*w*n*(q+1-s) := by field_simp <;> ring
  have hright : n^2*(1/n+(2*w/n)*q+2*(w-1/n)/n) = n+2*w*n*q+2*w*n-2 := by field_simp <;> ring
  rw [hleft,hright]
  nlinarith

/-- Sharp one-row conclusion after both cutoff losses have vanished. -/
theorem one_row_variable_success_limit {n p q : ℝ} (hn : 2 ≤ n)
    (h : ∀ w, 1/n < w → w < 1 →
      p ≤ 1/n+(2*w/n)*q+2*(w-1/n)/n) : n*(n*p-1)/2 ≤ q := by
  have hn0 : 0 < n := by linarith
  have ht := right_limit (b := 1/n-2/n^2) (c := 2*(q+1)/n)
    ((div_lt_one hn0).mpr (by linarith : 1<n)) (by
      intro w hw hw1
      have hh := h w hw hw1
      convert hh using 1 <;> field_simp <;> ring)
  have hp : p ≤ 1/n+(2/n^2)*q := by
    convert ht using 1 <;> field_simp <;> ring
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg n)
  have heq : n^2*(1/n+(2/n^2)*q)=n+2*q := by field_simp
  rw [heq] at hm
  nlinarith

end EnvyFreeResearch.Full.MoatLedger
