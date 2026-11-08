import Mathlib

/-! The actual population recursion permits a smaller single child or two
nonempty disjoint child populations. This tree charges ambient recording to
child Cuts, without multiplying inherited child query counts. -/

namespace EnvyFreeResearch.Full.Chores.Population

inductive Tree : ℕ → Type
  | leaf {n : ℕ} (positive : 0 < n) : Tree n
  | one {n k : ℕ} (smaller : k < n) (child : Tree k) : Tree n
  | two {b c : ℕ} (left : Tree b) (right : Tree c) : Tree (b + c)

namespace Tree

variable {n : ℕ}

def nodes : {n : ℕ} → Tree n → ℕ
  | _, .leaf _ => 1
  | _, .one _ child => 1 + nodes child
  | _, .two left right => 1 + nodes left + nodes right

theorem positive (tree : Tree n) : 0 < n := by
  induction tree with
  | leaf h => exact h
  | one h child ih => omega
  | two left right ihl ihr => omega

/-- The unary domination branch strictly discards agents; a binary branch
has disjoint populations. Both are included in the 2n-1 node bound. -/
theorem nodes_le (tree : Tree n) : tree.nodes ≤ 2*n-1 := by
  induction tree with
  | leaf h => simp only [nodes]; omega
  | @one n k h child ih =>
    have hp := child.positive
    simp only [nodes]
    omega
  | @two b c left right ihl ihr =>
    have hb := left.positive
    have hc := right.positive
    simp only [nodes]
    omega

def sum (localCost : ℕ → ℕ) : {n : ℕ} → Tree n → ℕ
  | n, .leaf _ => localCost n
  | n, .one _ child => localCost n + sum localCost child
  | _, @Tree.two b c left right => localCost (b+c) + sum localCost left + sum localCost right

/-- The Cut ledger is additive through recursive calls. -/
def cuts (localCuts : ℕ → ℕ) (tree : Tree n) : ℕ := tree.sum localCuts

/-- At each node, a native child executes all its own queries unchanged.
Only its new Cut-created endpoints cost the current population size again. -/
def queries (localQueries localCuts : ℕ → ℕ) : {n : ℕ} → Tree n → ℕ
  | n, .leaf _ => localQueries n
  | n, .one _ child => localQueries n + queries localQueries localCuts child + n * child.cuts localCuts
  | _, @Tree.two b c left right => localQueries (b+c) + queries localQueries localCuts left + queries localQueries localCuts right +
      (b+c) * (left.cuts localCuts + right.cuts localCuts)

theorem square_step {k n : ℕ} (hk : k < n) : k^2 + n ≤ n^2 := by
  have hkn : k + 1 ≤ n := hk
  have hprod := Nat.mul_le_mul_right n hkn
  have hprod' := Nat.mul_le_mul_left k (Nat.le_of_lt hk)
  nlinarith

/-- Every Cut is revisited at most once per ancestor, with ancestor population
at most n. The total ambient recording charge is bounded by n² times all
local Cuts, independently of the much larger local query counts. -/
theorem queries_le (localQueries localCuts : ℕ → ℕ) (tree : Tree n) :
    tree.queries localQueries localCuts ≤ tree.sum localQueries + n^2 * tree.cuts localCuts := by
  induction tree with
  | leaf h => simp [queries, sum, cuts]
  | @one n k h child ih =>
    have hs := square_step h
    calc
      queries localQueries localCuts (.one h child) =
          localQueries n + queries localQueries localCuts child + n * child.cuts localCuts := rfl
      _ ≤ localQueries n + (child.sum localQueries + k^2 * child.cuts localCuts) + n * child.cuts localCuts :=
          Nat.add_le_add_right (Nat.add_le_add_left ih _) _
      _ = localQueries n + child.sum localQueries + (k^2+n) * child.cuts localCuts := by ring
      _ ≤ localQueries n + child.sum localQueries + n^2 * child.cuts localCuts :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _
      _ ≤ sum localQueries (.one h child) + n^2 * cuts localCuts (.one h child) := by
          simp only [sum, cuts, Nat.mul_add]
          omega
  | @two b c left right ihl ihr =>
    have hb := left.positive
    have hc := right.positive
    have hsB := square_step (show b < b+c by omega)
    have hsC := square_step (show c < b+c by omega)
    calc
      queries localQueries localCuts (.two left right) =
          localQueries (b+c) + queries localQueries localCuts left + queries localQueries localCuts right +
            (b+c) * (left.cuts localCuts + right.cuts localCuts) := rfl
      _ ≤ localQueries (b+c) + (left.sum localQueries+b^2*left.cuts localCuts) +
          (right.sum localQueries+c^2*right.cuts localCuts) +
            (b+c) * (left.cuts localCuts+right.cuts localCuts) := by omega
      _ = localQueries (b+c) + left.sum localQueries + right.sum localQueries +
          (b^2+(b+c))*left.cuts localCuts + (c^2+(b+c))*right.cuts localCuts := by ring
      _ ≤ localQueries (b+c) + left.sum localQueries + right.sum localQueries +
          (b+c)^2*left.cuts localCuts + (b+c)^2*right.cuts localCuts :=
          Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hsB) _)
            (Nat.mul_le_mul_right _ hsC)
      _ ≤ sum localQueries (.two left right) + (b+c)^2 * cuts localCuts (.two left right) := by
          simp only [sum, cuts, Nat.mul_add]
          omega

theorem sum_le (localCost : ℕ → ℕ) (tree : Tree n) (bound : ℕ)
    (hbound : ∀ k, 0 < k → k ≤ n → localCost k ≤ bound) :
    tree.sum localCost ≤ tree.nodes * bound := by
  induction tree with
  | @leaf n h => simpa only [sum, nodes, one_mul] using hbound n h le_rfl
  | @one n k h child ih =>
    have hlocal := hbound n (child.positive.trans h) le_rfl
    have hchild := ih (fun j hj hjk => hbound j hj (hjk.trans h.le))
    simp only [sum, nodes, Nat.add_mul, one_mul]
    omega
  | @two b c left right ihl ihr =>
    have hlocal := hbound (b+c) (by have := left.positive; omega) le_rfl
    have hl := ihl (fun j hj hjb => hbound j hj (by omega))
    have hr := ihr (fun j hj hjc => hbound j hj (by omega))
    simp only [sum, nodes, Nat.add_mul, one_mul]
    omega

/-- Uniform local envelopes give explicit global Q/C envelopes, with only a
polynomial charge for all ancestor recordings. -/
theorem ledger_bound (localQueries localCuts : ℕ → ℕ) (tree : Tree n) (MQ MC : ℕ)
    (hQ : ∀ k, 0 < k → k ≤ n → localQueries k ≤ MQ)
    (hC : ∀ k, 0 < k → k ≤ n → localCuts k ≤ MC) :
    tree.cuts localCuts ≤ (2*n-1)*MC ∧
      tree.queries localQueries localCuts ≤ (2*n-1)*(MQ+n^2*MC) := by
  have hq := tree.sum_le localQueries MQ hQ
  have hc := tree.sum_le localCuts MC hC
  have hn := tree.nodes_le
  constructor
  · exact hc.trans (Nat.mul_le_mul_right MC hn)
  · calc
      tree.queries localQueries localCuts ≤ tree.sum localQueries+n^2*tree.cuts localCuts :=
        tree.queries_le localQueries localCuts
      _ ≤ tree.nodes*MQ+n^2*(tree.nodes*MC) := Nat.add_le_add hq (Nat.mul_le_mul_left _ hc)
      _ = tree.nodes*(MQ+n^2*MC) := by ring
      _ ≤ (2*n-1)*(MQ+n^2*MC) := Nat.mul_le_mul_right _ hn

end Tree
end EnvyFreeResearch.Full.Chores.Population
