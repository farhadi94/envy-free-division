import Mathlib

/-! Concrete deterministic-algorithm parameters and their binary envelopes.
These are arithmetic proofs, to be joined to the actual scheduler's separate
ordinary-query and Cut ledgers. -/

namespace EnvyFreeResearch.Full.Chores.Parameters

def ell (n : ℕ) : ℕ := Nat.clog 2 n
def weight (n : ℕ) : ℕ := n * (ell n + 1)
def classes (n : ℕ) : ℕ := n * (4^n + 2^n)
def exponent (n : ℕ) : ℕ := 3*n - 2
def selected (n : ℕ) : ℕ := (classes n+n^2+1)*(n+1)^exponent n
def roots (n : ℕ) : ℕ := (selected n-1)*(n-1)+1
def scale (n : ℕ) : ℕ := 2^(n+5)*roots n*n^3
def tracked (n : ℕ) : ℕ := roots n*(n^3+n^2)
def length (n : ℕ) : ℕ := 14*n*weight n

theorem le_two_pow_ell (n : ℕ) : n ≤ 2^ell n := Nat.le_pow_clog (by decide) n

theorem ell_le (n : ℕ) : ell n ≤ n := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem ell_lower {n : ℕ} (hn : 3 ≤ n) : 2 ≤ ell n := by
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by norm_num; omega)

theorem weight_lower {n : ℕ} (hn : 3 ≤ n) : 3*n ≤ weight n := by
  have he := ell_lower hn
  unfold weight
  nlinarith

theorem weight_mono : Monotone weight := by
  intro n m hnm
  exact Nat.mul_le_mul hnm (Nat.add_le_add_right (Nat.clog_mono_right 2 hnm) 1)

theorem selected_pos (n : ℕ) : 0 < selected n := by
  unfold selected
  exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

theorem roots_pos (n : ℕ) : 0 < roots n := by unfold roots; omega

theorem roots_le {n : ℕ} (hn : 1 ≤ n) : roots n ≤ n*selected n := by
  have hs := selected_pos n
  have hs' : selected n-1+1 = selected n := Nat.sub_add_cancel hs
  have hn' : n-1+1 = n := Nat.sub_add_cancel hn
  unfold roots
  nlinarith

theorem classes_base_le {n : ℕ} (hn : 1 ≤ n) : classes n+n^2+1 ≤ 4*n*4^n := by
  have htwo : 2^n ≤ 4^n := Nat.pow_le_pow_left (by decide) n
  have hnpow : n ≤ 4^n := (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))).trans htwo
  have hnterm : 1 ≤ n*4^n := by
    simpa using Nat.mul_le_mul hn (Nat.one_le_pow n 4 (by decide))
  have hsq : n^2 ≤ n*4^n := by simpa only [pow_two] using Nat.mul_le_mul_left n hnpow
  have hpow := Nat.mul_le_mul_left n htwo
  unfold classes
  nlinarith

theorem four_pow (n : ℕ) : (4 : ℕ)^n = 2^(2*n) := by rw [pow_mul]; rfl

theorem base_binary {n : ℕ} (hn : 1 ≤ n) : classes n+n^2+1 ≤ 2^(2+ell n+2*n) := by
  calc
    classes n+n^2+1 ≤ 4*n*4^n := classes_base_le hn
    _ ≤ 4*(2^ell n)*4^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (le_two_pow_ell n))
    _ = 2^(2+ell n+2*n) := by rw [four_pow]; simp only [pow_add]; norm_num

theorem next_binary (n : ℕ) : n+1 ≤ 2^(ell n+1) := by
  have hn := le_two_pow_ell n
  have hpos : 1 ≤ 2^ell n := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem selected_binary {n : ℕ} (hn : 3 ≤ n) : selected n ≤ 2^(4*weight n) := by
  have he := ell_lower hn
  have hsub : exponent n+2 = 3*n := by unfold exponent; omega
  have hexp : 2+ell n+2*n+(ell n+1)*exponent n ≤ 4*weight n := by
    unfold weight
    nlinarith
  calc
    selected n ≤ 2^(2+ell n+2*n)*(2^(ell n+1))^exponent n :=
      Nat.mul_le_mul (base_binary (by omega)) (Nat.pow_le_pow_left (next_binary n) _)
    _ = 2^(2+ell n+2*n+(ell n+1)*exponent n) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2^(4*weight n) := Nat.pow_le_pow_right (by decide) hexp

theorem roots_binary {n : ℕ} (hn : 3 ≤ n) : roots n ≤ 2^(5*weight n) := by
  have hn1 : 1 ≤ n := by omega
  have hew : ell n ≤ weight n := by unfold weight; nlinarith
  calc
    roots n ≤ n*selected n := roots_le hn1
    _ ≤ 2^ell n*2^(4*weight n) := Nat.mul_le_mul (le_two_pow_ell n) (selected_binary hn)
    _ = 2^(ell n+4*weight n) := (pow_add _ _ _).symm
    _ ≤ 2^(5*weight n) := Nat.pow_le_pow_right (by decide) (by omega)

theorem scale_binary {n : ℕ} (hn : 3 ≤ n) : scale n ≤ 2^(7*weight n) := by
  have he := ell_le n
  have hw := weight_lower hn
  have hexp : n+5+5*weight n+ell n*3 ≤ 7*weight n := by omega
  calc
    scale n ≤ 2^(n+5)*2^(5*weight n)*(2^ell n)^3 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (roots_binary hn)) (Nat.pow_le_pow_left (le_two_pow_ell n) 3)
    _ = 2^(n+5+5*weight n+ell n*3) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2^(7*weight n) := Nat.pow_le_pow_right (by decide) hexp

theorem scale_squared_binary {n : ℕ} (hn : 3 ≤ n) : (scale n)^2 ≤ 2^(14*weight n) := by
  calc
    (scale n)^2 ≤ (2^(7*weight n))^2 := Nat.pow_le_pow_left (scale_binary hn) 2
    _ = 2^(14*weight n) := by rw [← pow_mul]; congr 1; ring

theorem ell_succ_binary (n : ℕ) : ell n+1 ≤ 2^ell n := Nat.lt_two_pow_self

theorem clearance_factor_binary {n : ℕ} (hn : 3 ≤ n) :
    29*n^5*(ell n+1) ≤ 2^(3*weight n) := by
  have he := ell_lower hn
  have hexp : 5+ell n*5+ell n ≤ 3*weight n := by unfold weight; nlinarith
  calc
    29*n^5*(ell n+1) ≤ 32*(2^ell n)^5*2^ell n :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (le_two_pow_ell n) 5))
        (ell_succ_binary n)
    _ = 2^(5+ell n*5+ell n) := by rw [← pow_mul]; simp only [pow_add]; norm_num
    _ ≤ 2^(3*weight n) := Nat.pow_le_pow_right (by decide) hexp

theorem snapshots_le {n : ℕ} (hn : 3 ≤ n) :
    roots n+tracked n*length n ≤ roots n*2^(3*weight n) := by
  have hn1 : 1 ≤ n := by omega
  have hw : 1 ≤ weight n := by have := weight_lower hn; omega
  have hn2 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn1 (by decide)
  have hterm : 1 ≤ n^4*weight n := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow 4 n hn1) hw
  have hpoly : roots n+tracked n*length n ≤ roots n*(29*n^5*(ell n+1)) := by
    have hleft : roots n+tracked n*length n ≤ 29*roots n*n^4*weight n := by
      unfold tracked length
      nlinarith [Nat.mul_le_mul_left (14*roots n*n*weight n) hn2,
        Nat.mul_le_mul_left (roots n) hterm]
    calc
      _ ≤ 29*roots n*n^4*weight n := hleft
      _ = _ := by unfold weight; ring
  exact hpoly.trans (Nat.mul_le_mul_left _ (clearance_factor_binary hn))

end EnvyFreeResearch.Full.Chores.Parameters
