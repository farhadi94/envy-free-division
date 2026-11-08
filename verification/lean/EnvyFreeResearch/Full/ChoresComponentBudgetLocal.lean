import EnvyFreeResearch.Full.ChoresComponentParameters
import EnvyFreeResearch.Full.ChoresComponentRecordedSubCore
import EnvyFreeResearch.Full.ChoresSnapshot
import EnvyFreeResearch.Full.ChoresClearanceLength

/-! Explicit envelopes for the actual snapshot and recorded compensation
budgets. Queries and Cuts remain separate. The generic physical interpreter
overhead and final retained-piece Evals are included in these arithmetic
expressions; the outer driver must still prove its actual group counts. -/

namespace EnvyFreeResearch.Full.Chores.Parameters
open IntervalCore

def snapshots (n : ℕ) : ℕ := roots n+tracked n*length n
def referenceBudget (n : ℕ) : ℕ := snapshots n*IntervalCore.queryBudget n+
  roots n*(n*2^(n+1))+19*n*2^n
def localQueries (n : ℕ) : ℕ := snapshots n*Snapshot.queryBudget n+
  roots n*ComponentRecording.budget n n+19*n*2^n
def localCuts (n : ℕ) : ℕ := snapshots n*Snapshot.cutBudget n+
  roots n*SubCore.sourceBudget n+19*2^n

theorem trim_polynomial (n : ℕ) : trimBudget n ≤ n^2*4^n := by
  apply Nat.mul_le_mul_left
  calc
    (2*(n-1)).choose (n-1)-1 ≤ (2*(n-1)).choose (n-1) := Nat.sub_le _ _
    _ ≤ 2^(2*(n-1)) := Nat.choose_le_two_pow _ _
    _ ≤ 2^(2*n) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^n := (four_pow n).symm

theorem core_polynomial {n : ℕ} (hn : 1 ≤ n) : IntervalCore.queryBudget n ≤ 2*n^3*4^n := by
  have hpow : 1 ≤ 4^n := Nat.one_le_pow n 4 (by decide)
  have hsquare : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
  have hlarge : n^2 ≤ n^3*4^n := hsquare.trans (by simpa using Nat.mul_le_mul_left (n^3) hpow)
  have ht := Nat.mul_le_mul_left n (trim_polynomial n)
  unfold IntervalCore.queryBudget
  nlinarith

theorem core_binary {n : ℕ} (hn : 3 ≤ n) : IntervalCore.queryBudget n ≤ 2^(3*weight n) := by
  have he := ell_lower hn
  have hm := Nat.mul_le_mul_right (ell n) hn
  have hexp : 1+ell n*3+2*n ≤ 3*weight n := by unfold weight; nlinarith
  calc
    IntervalCore.queryBudget n ≤ 2*n^3*4^n := core_polynomial (by omega)
    _ ≤ 2*(2^ell n)^3*4^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_two_pow_ell n) 3))
    _ = 2^(1+ell n*3+2*n) := by rw [four_pow, ← pow_mul]; simp only [pow_add]; norm_num
    _ ≤ 2^(3*weight n) := Nat.pow_le_pow_right (by decide) hexp

theorem group_binary {n : ℕ} (hn : 3 ≤ n) : n*2^(n+1) ≤ 2^weight n := by
  have he := ell_lower hn
  have hm := Nat.mul_le_mul_right (ell n) hn
  have hexp : ell n+n+1 ≤ weight n := by unfold weight; nlinarith
  calc
    n*2^(n+1) ≤ 2^ell n*2^(n+1) := Nat.mul_le_mul_right _ (le_two_pow_ell n)
    _ = 2^(ell n+n+1) := by rw [← pow_add]; congr 1
    _ ≤ 2^weight n := Nat.pow_le_pow_right (by decide) hexp

theorem completion_binary {n : ℕ} (hn : 3 ≤ n) : 19*n*2^n ≤ 2^(2*weight n) := by
  have he := ell_le n
  have hw := weight_lower hn
  have hexp : 5+ell n+n ≤ 2*weight n := by omega
  calc
    19*n*2^n ≤ 32*2^ell n*2^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) (le_two_pow_ell n))
    _ = 2^(5+ell n+n) := by simp only [pow_add]; norm_num
    _ ≤ 2^(2*weight n) := Nat.pow_le_pow_right (by decide) hexp

theorem reference_binary {n : ℕ} (hn : 3 ≤ n) : referenceBudget n ≤ 2^(12*weight n) := by
  have hpre : snapshots n*IntervalCore.queryBudget n ≤ 2^(11*weight n) := by
    calc
      _ ≤ (roots n*2^(3*weight n))*2^(3*weight n) := Nat.mul_le_mul (snapshots_le hn) (core_binary hn)
      _ ≤ (2^(5*weight n)*2^(3*weight n))*2^(3*weight n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (roots_binary hn))
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; ring
  have hgroup : roots n*(n*2^(n+1)) ≤ 2^(6*weight n) := by
    calc
      _ ≤ 2^(5*weight n)*2^weight n := Nat.mul_le_mul (roots_binary hn) (group_binary hn)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hgroup' := hgroup.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 6*weight n ≤ 11*weight n))
  have hcomplete := (completion_binary hn).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2*weight n ≤ 11*weight n))
  have hw := weight_lower hn
  have hthree : 3 ≤ 2^weight n := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ weight n by omega)
    norm_num at hh
    omega
  calc
    referenceBudget n ≤ 3*2^(11*weight n) := by unfold referenceBudget; omega
    _ ≤ 2^weight n*2^(11*weight n) := Nat.mul_le_mul_right _ hthree
    _ = 2^(12*weight n) := by rw [← pow_add]; congr 1; ring

theorem snapshot_queries_le {n : ℕ} (hn : 3 ≤ n) :
    Snapshot.queryBudget n ≤ 5*n*IntervalCore.queryBudget n := by
  have hn1 : 1 ≤ n := by omega
  have hsquare : n ≤ n^2 := by simpa using Nat.pow_le_pow_right hn1 (show 1 ≤ 2 by decide)
  have ht : trimBudget n ≤ n*trimBudget n := by simpa using Nat.mul_le_mul_right (trimBudget n) hn1
  have hsmall : n-1+trimBudget n ≤ IntervalCore.queryBudget n := by
    unfold IntervalCore.queryBudget
    omega
  have hsmall' := Nat.mul_le_mul_left n hsmall
  have hcore : n^2 ≤ IntervalCore.queryBudget n := Nat.le_add_right _ _
  have hcore' := Nat.mul_le_mul_left (2*n) hcore
  have hcube := Nat.mul_le_mul_right (n^2) hn
  unfold Snapshot.queryBudget OrderedUnion.cachedDomainCoreBudget OrderedUnion.domainCoreBudget
  nlinarith

theorem snapshot_cuts_le {n : ℕ} (hn : 1 ≤ n) :
    Snapshot.cutBudget n ≤ 2*IntervalCore.queryBudget n := by
  have hsquare : n ≤ n^2 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 2 by decide)
  have ht : trimBudget n ≤ n*trimBudget n := by simpa using Nat.mul_le_mul_right (trimBudget n) hn
  unfold Snapshot.cutBudget IntervalCore.queryBudget
  omega

theorem source_le_power (n : ℕ) : SubCore.sourceBudget n ≤ 2^(n+1) := by
  have h := SubCore.sourceBudget_closed n
  omega

theorem recorded_queries_le {n : ℕ} (hn : 1 ≤ n) :
    ComponentRecording.budget n n ≤ 5*n*(n*2^(n+1)) := by
  have hsquare : n ≤ n^2 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 2 by decide)
  have hc : n*(2*n+1) ≤ 3*n^2 := by nlinarith
  have ht := Nat.mul_le_mul hc (source_le_power n)
  have hp : n^2 ≤ n^2*2^(n+1) := by simpa using Nat.mul_le_mul_left (n^2) (Nat.one_le_two_pow (n := n+1))
  rw [ComponentRecording.budget_eq]
  nlinarith

theorem actual_queries_reference {n : ℕ} (hn : 3 ≤ n) : localQueries n ≤ 5*n*referenceBudget n := by
  have hp := Nat.mul_le_mul_left (snapshots n) (snapshot_queries_le hn)
  have hg := Nat.mul_le_mul_left (roots n) (recorded_queries_le (by omega : 1 ≤ n))
  have hf : 19*n*2^n ≤ 5*n*(19*n*2^n) := by
    simpa using Nat.mul_le_mul_right (19*n*2^n) (show 1 ≤ 5*n by omega)
  unfold localQueries referenceBudget
  nlinarith

theorem actual_cuts_reference {n : ℕ} (hn : 3 ≤ n) : localCuts n ≤ 2*referenceBudget n := by
  have hn1 : 1 ≤ n := by omega
  have hp := Nat.mul_le_mul_left (snapshots n) (snapshot_cuts_le hn1)
  have hg : SubCore.sourceBudget n ≤ n*2^(n+1) := (source_le_power n).trans (by
    simpa using Nat.mul_le_mul_right (2^(n+1)) hn1)
  have hg' := Nat.mul_le_mul_left (roots n) hg
  have hf : 19*2^n ≤ 19*n*2^n := by nlinarith [Nat.mul_le_mul_right (19*2^n) hn1]
  unfold localCuts referenceBudget
  nlinarith [Nat.zero_le (roots n*(n*2^(n+1))), Nat.zero_le (19*n*2^n)]

theorem actual_queries_binary {n : ℕ} (hn : 3 ≤ n) : localQueries n ≤ 5*n*2^(12*weight n) :=
  (actual_queries_reference hn).trans (Nat.mul_le_mul_left _ (reference_binary hn))

theorem actual_cuts_binary {n : ℕ} (hn : 3 ≤ n) : localCuts n ≤ 2*2^(12*weight n) :=
  (actual_cuts_reference hn).trans (Nat.mul_le_mul_left _ (reference_binary hn))

theorem clearance_length {n : ℕ} (hn : 3 ≤ n) :
    (scale n : ℝ)*Snapshot.contraction n^length n ≤ 1/(scale n : ℝ) := by
  have hscale : 0 < scale n := by
    have hroot := roots_pos n
    have hnpos : 0 < n := by omega
    unfold scale
    positivity
  have hbound : (scale n : ℝ)*(scale n : ℝ) ≤ (2 : ℝ)^(14*weight n) := by
    have h := scale_squared_binary hn
    exact_mod_cast (show scale n*scale n ≤ 2^(14*weight n) by simpa only [pow_two] using h)
  have h := Clearance.length_from_power_bound (show 2 ≤ n by omega) (scale n : ℝ)
    (by exact_mod_cast hscale) (14*weight n) hbound
  simpa only [length, show n*(14*weight n) = 14*n*weight n by ring] using h

end EnvyFreeResearch.Full.Chores.Parameters
