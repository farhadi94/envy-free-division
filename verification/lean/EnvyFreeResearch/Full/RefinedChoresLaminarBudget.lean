import Mathlib

/-!
The factorial weight bound for a binary completion of a proper paid-component
hierarchy.  This isolates the combinatorial inequality behind the proposed
asynchronous pool size.  Constructing that hierarchy from the actual scheduler
is a separate obligation: the results here do not assert an oracle protocol.
-/
namespace EnvyFreeResearch.Full.RefinedChoresLaminarBudget
open scoped Nat

/-- Joining two nonempty blocks is most expensive when one is a singleton. -/
theorem factorial_pair {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a + 1)! * (b + 1)! ≤ 2 * (a + b)! := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction t with
  | zero => simp [Nat.add_comm, Nat.mul_comm]
  | succ t ih =>
    have hstep : (1 + t + 2) ≤ a + (1 + t) + 1 := by omega
    calc
      (a + 1)! * (1 + (t + 1) + 1)! =
          (1 + t + 2) * ((a + 1)! * (1 + t + 1)!) := by
        rw [show 1 + (t + 1) + 1 = (1 + t + 1) + 1 by omega, Nat.factorial_succ (1 + t + 1)]
        ring
      _ ≤ (1 + t + 2) * (2 * (a + (1 + t))!) := Nat.mul_le_mul_left _ (ih (by omega))
      _ ≤ (a + (1 + t) + 1) * (2 * (a + (1 + t))!) := Nat.mul_le_mul_right _ hstep
      _ = 2 * (a + (1 + (t + 1)))! := by
        rw [show a + (1 + (t + 1)) = (a + (1 + t)) + 1 by omega, Nat.factorial_succ]
        ring

/-- A binary completion can include unpaid nodes. Paying every proper node
only increases the product, so the all-paid product is a useful envelope. -/
inductive Tree where
  | leaf
  | join (left right : Tree)
deriving DecidableEq

def Tree.size : Tree → ℕ
  | .leaf => 1
  | .join a b => a.size + b.size

def Tree.weight : Tree → ℕ
  | .leaf => 2
  | .join a b => (a.size + b.size + 1) * a.weight * b.weight

def Tree.properWeight : Tree → ℕ
  | .leaf => 1
  | .join a b => a.weight * b.weight

theorem Tree.size_pos (t : Tree) : 1 ≤ t.size := by
  induction t with
  | leaf => rfl
  | join a b ha hb => simp only [Tree.size]; omega

theorem Tree.weight_bound (t : Tree) : t.weight ≤ 2^(t.size - 1) * (t.size + 1)! := by
  induction t with
  | leaf => norm_num [Tree.size, Tree.weight]
  | join a b ha hb =>
    have hapos := a.size_pos
    have hbpos := b.size_pos
    have hf := factorial_pair hapos hbpos
    have hpow : 2^(a.size - 1) * 2^(b.size - 1) * 2 = 2^(a.size + b.size - 1) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    change (a.size + b.size + 1) * a.weight * b.weight ≤ _
    calc
      _ ≤ (a.size + b.size + 1) * (2^(a.size - 1) * (a.size + 1)!) *
          (2^(b.size - 1) * (b.size + 1)!) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hb
      _ = (a.size + b.size + 1) * (2^(a.size - 1) * 2^(b.size - 1)) *
          ((a.size + 1)! * (b.size + 1)!) := by ring
      _ ≤ (a.size + b.size + 1) * (2^(a.size - 1) * 2^(b.size - 1)) *
          (2 * (a.size + b.size)!) := Nat.mul_le_mul_left _ hf
      _ = 2^(a.size + b.size - 1) * (a.size + b.size + 1)! := by
        rw [Nat.factorial_succ, ← hpow]
        ring

theorem Tree.properWeight_bound (t : Tree) : t.properWeight ≤ 2^(t.size - 1) * (t.size)! := by
  cases t with
  | leaf => norm_num [Tree.properWeight, Tree.size]
  | join a b =>
    have hapos := a.size_pos
    have hbpos := b.size_pos
    have hf := factorial_pair hapos hbpos
    have hpow : 2^(a.size - 1) * 2^(b.size - 1) * 2 = 2^(a.size + b.size - 1) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    change a.weight * b.weight ≤ 2^(a.size + b.size - 1) * (a.size + b.size)!
    calc
      _ ≤ (2^(a.size - 1) * (a.size + 1)!) * (2^(b.size - 1) * (b.size + 1)!) :=
        Nat.mul_le_mul a.weight_bound b.weight_bound
      _ = (2^(a.size - 1) * 2^(b.size - 1)) * ((a.size + 1)! * (b.size + 1)!) := by ring
      _ ≤ (2^(a.size - 1) * 2^(b.size - 1)) * (2 * (a.size + b.size)!) :=
        Nat.mul_le_mul_left _ hf
      _ = _ := by rw [← mul_assoc, hpow]

def packageCap (n : ℕ) : ℕ := 2^(n-1) * (n)!
def liveCap (n : ℕ) : ℕ := 2*n*8^n
def poolSize (n : ℕ) : ℕ := n * (n)! * 16^n + 1

/-- The proposed pool is strictly larger than live-count times package size.
This is an exact integer inequality, not a numerical spot check. -/
theorem pool_surplus {n : ℕ} (hn : 1 ≤ n) : liveCap n * packageCap n < poolSize n := by
  have hp : 2 * 2^(n-1) = 2^n := by
    rw [← pow_succ']
    congr 1
    omega
  have he : liveCap n * packageCap n = n * (n)! * 16^n := by
    unfold liveCap packageCap
    calc
      2 * n * 8^n * (2^(n-1) * (n)!) = n * (n)! * (8^n * (2 * 2^(n-1))) := by ring
      _ = n * (n)! * (8^n * 2^n) := by rw [hp]
      _ = n * (n)! * 16^n := by rw [← mul_pow]; norm_num
  rw [he, poolSize]
  omega

/-- A partition of the pool into at most `liveCap n` packages of the bounded
size is impossible. The scheduler still has to establish both hypotheses. -/
theorem no_stall_from_counts {n : ℕ} (hn : 1 ≤ n) (weights : List ℕ)
    (hlen : weights.length ≤ liveCap n) (hweights : ∀ w ∈ weights, w ≤ packageCap n)
    (hpartition : weights.sum = poolSize n) : False := by
  have hsum : ∀ l : List ℕ, (∀ w ∈ l, w ≤ packageCap n) → l.sum ≤ l.length * packageCap n := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      have ha := h a (by simp)
      have hl := ih (fun w hw => h w (by simp [hw]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith
  have hle := (hsum weights hweights).trans (Nat.mul_le_mul_right _ hlen)
  rw [hpartition] at hle
  exact (not_le_of_gt (pool_surplus hn)) hle

end EnvyFreeResearch.Full.RefinedChoresLaminarBudget

#print axioms EnvyFreeResearch.Full.RefinedChoresLaminarBudget.Tree.properWeight_bound
#print axioms EnvyFreeResearch.Full.RefinedChoresLaminarBudget.pool_surplus
