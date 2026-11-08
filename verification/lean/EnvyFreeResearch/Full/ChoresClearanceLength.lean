import EnvyFreeResearch.Full.ChoresClearanceGeometry
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform lengths for a clearance block. Bernoulli's inequality gives
strict halving after n Core calls. Consequently, a power-of-two upper bound
on H² gives a concrete length n*k, independent of all valuation data. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Clearance
open Snapshot

theorem contraction_lt_one {n : ℕ} (hn : 2 ≤ n) : contraction n < 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_lt_one hnpos).mpr
  exact_mod_cast (by omega : n-1 < n)

theorem exists_clearance_length {n : ℕ} (hn : 2 ≤ n) (H : ℝ) (hH : 0 < H) :
    ∃ L : ℕ, H*contraction n^L ≤ 1/H := by
  obtain ⟨L,hL⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1/(H*H) by positivity)
    (contraction_lt_one hn)
  refine ⟨L,?_⟩
  have h := mul_le_mul_of_nonneg_left hL.le hH.le
  have heq : H*(1/(H*H)) = 1/H := by field_simp
  exact h.trans_eq heq

theorem contraction_halves {n : ℕ} (hn : 2 ≤ n) : contraction n^n < (1/2 : ℝ) := by
  let a : ℝ := (n-1 : ℕ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (by omega : 0 < n-1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsum : a+1 = (n : ℝ) := by
    dsimp [a]
    exact_mod_cast (show n-1+1 = n by omega)
  have hratio : 1 < (n : ℝ)/a := (one_lt_div ha).mpr (by linarith)
  have hnonneg : 0 ≤ 1/a := by positivity
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1/a by linarith) n
  have hlarge : (2 : ℝ) < (1+1/a)^n := by
    have hratio' : 1 < (n : ℝ)*(1/a) := by simpa only [div_eq_mul_inv,one_mul] using hratio
    linarith
  have hprod : contraction n*(1+1/a) = 1 := by
    change (a/(n : ℝ))*(1+1/a) = 1
    field_simp
    nlinarith
  have hpowprod : contraction n^n*(1+1/a)^n = 1 := by rw [← mul_pow,hprod,one_pow]
  have hpositive : 0 < contraction n^n := pow_pos (div_pos ha hnpos) n
  have hmul := mul_lt_mul_of_pos_left hlarge hpositive
  rw [hpowprod] at hmul
  linarith

theorem length_from_power_bound {n : ℕ} (hn : 2 ≤ n) (H : ℝ) (hH : 0 < H)
    (k : ℕ) (hbound : H*H ≤ (2 : ℝ)^k) : H*contraction n^(n*k) ≤ 1/H := by
  have hhalf : contraction n^(n*k) ≤ (1/2 : ℝ)^k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (contraction_nonneg n) n) (contraction_halves hn).le k
  have hproduct : contraction n^(n*k)*(2 : ℝ)^k ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hhalf (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k)
    have heq : (1/2 : ℝ)^k*(2 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
    exact h.trans_eq heq
  apply (le_div_iff₀ hH).mpr
  calc
    H*contraction n^(n*k)*H = contraction n^(n*k)*(H*H) := by ring
    _ ≤ contraction n^(n*k)*(2 : ℝ)^k :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg (contraction_nonneg n) _)
    _ ≤ 1 := hproduct

end EnvyFreeResearch.Full.Chores.Clearance
