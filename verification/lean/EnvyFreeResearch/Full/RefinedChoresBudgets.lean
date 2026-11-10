import EnvyFreeResearch.Full.RefinedChoresParameters
import EnvyFreeResearch.Full.ChoresComponentBudgetLocal
import EnvyFreeResearch.Full.ChoresComponentPopulationCapacity

/-! Separate scalar accounting for the actual preprocessing, paid-prefix,
terminal and completion calls. The final protocol must instantiate these
call counts before using the factorial population envelope. -/
namespace EnvyFreeResearch.Full.RefinedChoresParameters
open scoped Nat

def snapshots (n : ℕ) := roots n + roots n*(n^2+n^3)*length n
def localQueries (n : ℕ) := snapshots n*Chores.Snapshot.queryBudget n +
  (selected n+1)*Chores.ComponentRecording.budget n n + 19*n*2^n
def envelope (n : ℕ) := (Nat.factorial n)*2^(22*n+15)
noncomputable def totalCapacity (n : ℕ) := Chores.Population.capacity envelope envelope n

/-- Polynomial prefactors cost only a linear term in the binary exponent. -/
theorem polynomial_binary (n a b c K : ℕ) (hK : K ≤ 2^c) :
    K*n^a*(2^b)^n*(Nat.factorial n) ≤ (Nat.factorial n)*2^((a+b)*n+c) := by
  have hn := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))) a
  calc
    _ ≤ 2^c*(2^n)^a*(2^b)^n*(Nat.factorial n) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hn))
    _ = (Nat.factorial n)*2^((a+b)*n+c) := by
      rw [← pow_mul,← pow_mul]
      calc
        _ = (Nat.factorial n)*(2^c*2^(n*a)*2^(b*n)) := by ring
        _ = _ := by rw [← pow_add,← pow_add]; congr 2; ring

theorem snapshots_polynomial {n : ℕ} (hn : 1 ≤ n) : snapshots n ≤ 93*roots n*n^6 := by
  have hn2 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
  have hL := length_polynomial hn
  have hprod := Nat.mul_le_mul (show n^2+n^3 ≤ 2*n^3 by omega) hL
  have h := Nat.mul_le_mul_left (roots n) hprod
  have hunit := Nat.mul_le_mul_left (roots n) (Nat.one_le_pow 6 n hn)
  unfold snapshots
  nlinarith

theorem snapshot_queries_polynomial {n : ℕ} (hn : 3 ≤ n) :
    Chores.Snapshot.queryBudget n ≤ 10*n^4*4^n := by
  have h := (Chores.Parameters.snapshot_queries_le hn).trans
    (Nat.mul_le_mul_left (5*n) (Chores.Parameters.core_polynomial (by omega : 1 ≤ n)))
  exact h.trans_eq (by ring)

theorem preprocessing_queries_binary {n : ℕ} (hn : 3 ≤ n) :
    snapshots n*Chores.Snapshot.queryBudget n ≤ (Nat.factorial n)*2^(22*n+13) := by
  have h := Nat.mul_le_mul (snapshots_polynomial (by omega : 1 ≤ n)) (snapshot_queries_polynomial hn)
  have hpoly : snapshots n*Chores.Snapshot.queryBudget n ≤ 7440*n^15*128^n*(Nat.factorial n) := by
    calc
      _ ≤ (93*roots n*n^6)*(10*n^4*4^n) := h
      _ = 930*roots n*n^10*4^n := by ring
      _ ≤ 930*(8*n^5*32^n*(Nat.factorial n))*n^10*4^n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (roots_polynomial (by omega))))
      _ = 7440*n^15*128^n*(Nat.factorial n) := by
        have hp : (32:ℕ)^n*4^n=128^n := by rw [← mul_pow]; norm_num
        calc
          _ = 7440*n^15*(32^n*4^n)*(Nat.factorial n) := by ring
          _ = _ := by rw [hp]
  exact hpoly.trans (by simpa using polynomial_binary n 15 7 13 7440 (by norm_num))

theorem paid_queries_binary {n : ℕ} (hn : 3 ≤ n) :
    (selected n+1)*Chores.ComponentRecording.budget n n ≤ (Nat.factorial n)*2^(13*n+8) := by
  have hs : selected n+1 ≤ 2*roots n := by have := selected_le_roots (by omega : 2 ≤ n); have := roots_pos n; omega
  have hq : Chores.ComponentRecording.budget n n ≤ 5*n^2*2^(n+1) :=
    (Chores.Parameters.recorded_queries_le (by omega : 1 ≤ n)).trans_eq (by ring)
  have hpoly : (selected n+1)*Chores.ComponentRecording.budget n n ≤ 160*n^7*64^n*(Nat.factorial n) := by
    calc
      _ ≤ (2*roots n)*(5*n^2*2^(n+1)) := Nat.mul_le_mul hs hq
      _ = 20*roots n*n^2*2^n := by rw [pow_succ]; ring
      _ ≤ 20*(8*n^5*32^n*(Nat.factorial n))*n^2*2^n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (roots_polynomial (by omega))))
      _ = 160*n^7*64^n*(Nat.factorial n) := by
        have hp : (32:ℕ)^n*2^n=64^n := by rw [← mul_pow]; norm_num
        calc
          _ = 160*n^7*(32^n*2^n)*(Nat.factorial n) := by ring
          _ = _ := by rw [hp]
  exact hpoly.trans (by simpa using polynomial_binary n 7 6 8 160 (by norm_num))

theorem completion_queries_binary (n : ℕ) : 19*n*2^n ≤ (Nat.factorial n)*2^(2*n+5) := by
  have h : 19*n*2^n ≤ 19*n*2^n*(Nat.factorial n) := by
    simpa using Nat.mul_le_mul_left (19*n*2^n) (Nat.factorial_pos n)
  exact h.trans (by simpa using polynomial_binary n 1 1 5 19 (by norm_num))

theorem local_queries_envelope {n : ℕ} (hn : 3 ≤ n) : localQueries n ≤ envelope n := by
  have hpre := preprocessing_queries_binary hn
  have hpaid := (paid_queries_binary hn).trans
    (Nat.mul_le_mul_left ((Nat.factorial n)) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 13*n+8 ≤ 22*n+13)))
  have hfinish := (completion_queries_binary n).trans
    (Nat.mul_le_mul_left ((Nat.factorial n)) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2*n+5 ≤ 22*n+13)))
  have heq : 4*((Nat.factorial n)*2^(22*n+13)) = envelope n := by
    unfold envelope
    rw [show 22*n+15=(22*n+13)+2 by omega,pow_add]
    norm_num
    ring
  unfold localQueries
  nlinarith

theorem envelope_mono : Monotone envelope := by
  intro n m hnm
  apply Nat.mul_le_mul (Nat.factorial_le hnm)
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem total_capacity_envelope {n : ℕ} (hn : 1 ≤ n) :
    (totalCapacity n).queries ≤ (Nat.factorial n)*2^(25*n+17) ∧
      (totalCapacity n).cuts ≤ (Nat.factorial n)*2^(25*n+17) := by
  obtain ⟨hq,hc⟩ := Chores.Population.capacity_envelope envelope envelope n (envelope n) (envelope n)
    (fun k _ hkn => envelope_mono hkn) (fun k _ hkn => envelope_mono hkn)
  have hn2 : 1 ≤ n^2 := Nat.one_le_pow 2 n hn
  have hp : (2*n-1)*(1+n^2) ≤ 4*n^3 := by
    have := Nat.mul_le_mul (Nat.sub_le (2*n) 1) (show 1+n^2 ≤ 2*n^2 by omega)
    nlinarith
  have he : 4*n^3*envelope n ≤ (Nat.factorial n)*2^(25*n+17) := by
    have hpoly := polynomial_binary n 3 22 2 4 (by norm_num)
    have heq : 4*n^3*envelope n = (4*n^3*(2^22)^n*(Nat.factorial n))*2^15 := by
      unfold envelope
      rw [pow_add,pow_mul]
      ring
    rw [heq]
    apply (Nat.mul_le_mul_right (2^15) hpoly).trans_eq
    rw [mul_assoc,← pow_add]
  constructor
  · apply (hq.trans ?_).trans he
    calc
      _ = ((2*n-1)*(1+n^2))*envelope n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  · apply (hc.trans ?_).trans he
    apply Nat.mul_le_mul_right
    have hn3 : n ≤ n^3 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 3 by decide)
    omega

end EnvyFreeResearch.Full.RefinedChoresParameters
#print axioms EnvyFreeResearch.Full.RefinedChoresParameters.local_queries_envelope
#print axioms EnvyFreeResearch.Full.RefinedChoresParameters.total_capacity_envelope
