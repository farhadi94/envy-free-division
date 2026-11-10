import EnvyFreeResearch.Full.RefinedChoresPool
import EnvyFreeResearch.Full.ChoresClearanceLength

/-! Concrete parameters for the root-local protocol. The pool has factorial
rather than n^{3n} growth; clearance uses only a polynomial number of rounds
per tracked entry. These are scalar bounds awaiting the full protocol join. -/
namespace EnvyFreeResearch.Full.RefinedChoresParameters
open RefinedChoresPool RefinedChoresBucketCapacity
open scoped Nat

def selected (n : ℕ) := poolSize n
def roots (n : ℕ) := (selected n-1)*(n-1)+1
def scale (n : ℕ) := 2^(n+5)*roots n*n^3
def clearanceExponent (n : ℕ) := 2*n^2+28*n+16
def length (n : ℕ) := n*clearanceExponent n

theorem selected_pos (n : ℕ) : 0 < selected n := by unfold selected poolSize; omega

theorem roots_pos (n : ℕ) : 0 < roots n := by unfold roots; omega

theorem roots_le {n : ℕ} (hn : 1 ≤ n) : roots n ≤ n*selected n := by
  have hs := selected_pos n
  have hs' : selected n-1+1=selected n := Nat.sub_add_cancel hs
  have hn' : n-1+1=n := Nat.sub_add_cancel hn
  unfold roots
  nlinarith

theorem selected_le_roots {n : ℕ} (hn : 2 ≤ n) : selected n ≤ roots n := by
  have hs := selected_pos n
  have h := Nat.mul_le_mul_left (selected n-1) (show 1 ≤ n-1 by omega)
  unfold roots
  omega

theorem classes_polynomial {n : ℕ} (hn : 1 ≤ n) : classCount n ≤ 7*n^3*4^n := by
  have hpow : 2^n ≤ 4^n := Nat.pow_le_pow_left (by decide) n
  have hn3 : n ≤ n^3 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 3 by decide)
  have h₁ := Nat.mul_le_mul_right (4*n^2+1) (Nat.mul_le_mul_left n hpow)
  have h₂ := Nat.mul_le_mul_left n hpow
  have h₃ := Nat.mul_le_mul_right (4^n) hn3
  unfold classCount buckets
  nlinarith

theorem selected_polynomial {n : ℕ} (hn : 1 ≤ n) :
    selected n ≤ 8*n^4*32^n*(Nat.factorial n) := by
  have hu : unpaid n ≤ 8^n*(Nat.factorial n) := Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le n 1))
  have hc := Nat.mul_le_mul (Nat.mul_le_mul_left n (classes_polynomial hn)) hu
  have hbase : 1 ≤ n^4*32^n*(Nat.factorial n) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow 4 n hn) (Nat.one_le_pow n 32 (by decide)))
      (Nat.factorial_pos n)
  have heq : n*(7*n^3*4^n)*(8^n*(Nat.factorial n))=7*n^4*32^n*(Nat.factorial n) := by
    have hpow : (4:ℕ)^n*8^n=32^n := by rw [← mul_pow]; norm_num
    calc
      _ = 7*n^4*(4^n*8^n)*(Nat.factorial n) := by ring
      _ = _ := by rw [hpow]
  rw [heq] at hc
  unfold selected poolSize liveBound
  nlinarith

theorem roots_polynomial {n : ℕ} (hn : 1 ≤ n) : roots n ≤ 8*n^5*32^n*(Nat.factorial n) :=
  (roots_le hn).trans ((Nat.mul_le_mul_left n (selected_polynomial hn)).trans_eq (by ring))

theorem scale_polynomial {n : ℕ} (hn : 1 ≤ n) : scale n ≤ 256*n^8*64^n*(Nat.factorial n) := by
  have h := Nat.mul_le_mul_right (n^3) (Nat.mul_le_mul_left (2^(n+5)) (roots_polynomial hn))
  apply h.trans_eq
  have hpow : (2:ℕ)^n*32^n=64^n := by rw [← mul_pow]; norm_num
  calc
    _ = 256*n^8*(2^n*32^n)*(Nat.factorial n) := by rw [pow_add]; norm_num; ring
    _ = _ := by rw [hpow]

theorem scale_factorial_binary {n : ℕ} (hn : 1 ≤ n) : scale n ≤ (Nat.factorial n)*2^(14*n+8) := by
  have hn8 := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))) 8
  calc
    scale n ≤ 256*n^8*64^n*(Nat.factorial n) := scale_polynomial hn
    _ ≤ 256*(2^n)^8*64^n*(Nat.factorial n) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn8))
    _ = (Nat.factorial n)*2^(14*n+8) := by
      rw [show (256:ℕ)=2^8 by norm_num,show (64:ℕ)=2^6 by norm_num,← pow_mul,← pow_mul]
      calc
        _ = (Nat.factorial n)*(2^8*2^(n*8)*2^(6*n)) := by ring
        _ = _ := by
          rw [← pow_add,← pow_add]
          congr 2
          omega

theorem scale_binary {n : ℕ} (hn : 1 ≤ n) : scale n ≤ 2^(n^2+14*n+8) := by
  have hf : (Nat.factorial n) ≤ 2^(n^2) := by
    calc
      (Nat.factorial n) ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^n)^n := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))) n
      _ = 2^(n^2) := by rw [← pow_mul,pow_two]
  calc
    scale n ≤ (Nat.factorial n)*2^(14*n+8) := scale_factorial_binary hn
    _ ≤ 2^(n^2)*2^(14*n+8) := Nat.mul_le_mul_right _ hf
    _ = _ := by rw [← pow_add]; congr 1

theorem length_polynomial {n : ℕ} (hn : 1 ≤ n) : length n ≤ 46*n^3 := by
  have hn2 : n ≤ n^2 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 2 by decide)
  have h1 : 1 ≤ n^2 := Nat.one_le_pow 2 n hn
  unfold length clearanceExponent
  nlinarith

theorem clearance_length {n : ℕ} (hn : 2 ≤ n) :
    (scale n : ℝ)*Chores.Snapshot.contraction n^length n ≤ 1/(scale n : ℝ) := by
  have hs : 0 < scale n := by
    have hj := roots_pos n
    have hp : 0 < n := by omega
    unfold scale
    positivity
  have hb : scale n*scale n ≤ 2^(clearanceExponent n) := by
    have h := Nat.mul_le_mul (scale_binary (by omega : 1 ≤ n)) (scale_binary (by omega : 1 ≤ n))
    apply h.trans_eq
    rw [← pow_add]
    congr 1
    unfold clearanceExponent
    ring
  exact Chores.Clearance.length_from_power_bound hn (scale n) (by exact_mod_cast hs)
    (clearanceExponent n) (by exact_mod_cast hb)

end EnvyFreeResearch.Full.RefinedChoresParameters
#print axioms EnvyFreeResearch.Full.RefinedChoresParameters.selected_polynomial
#print axioms EnvyFreeResearch.Full.RefinedChoresParameters.clearance_length
