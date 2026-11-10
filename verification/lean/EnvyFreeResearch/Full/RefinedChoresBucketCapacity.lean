import EnvyFreeResearch.Full.RefinedChoresLaminarBudget

/-!
Dyadic grouping avoids counting exact products along paid lineages.
An unpaid component of size m has capacity U(m)=8^(m-1)m!; a paid
component has capacity P(m)=2(m+1)U(m). Paying increases the factor
by exactly 2(m+1), while merging paid components never decreases it.
These inequalities are intended for the root-local scheduler invariant.
-/
namespace EnvyFreeResearch.Full.RefinedChoresBucketCapacity
open scoped Nat
open RefinedChoresLaminarBudget

def unpaid (m : ℕ) : ℕ := 8^(m-1) * (m)!
def paid (m : ℕ) : ℕ := 2*(m+1)*unpaid m

theorem unpaid_pos (m : ℕ) : 0 < unpaid m := by
  unfold unpaid
  exact Nat.mul_pos (by positivity) (Nat.factorial_pos m)

theorem unpaid_le_paid (m : ℕ) : unpaid m ≤ paid m := by
  unfold paid
  have h : 1 ≤ 2*(m+1) := by omega
  simpa only [one_mul] using Nat.mul_le_mul_right (unpaid m) h

theorem paid_pair_le_unpaid {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    paid a * paid b ≤ unpaid (a+b) := by
  have hf := factorial_pair ha hb
  have hp : 8^(a-1)*8^(b-1)*8 = 8^(a+b-1) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  calc
    paid a * paid b = 4 * (8^(a-1)*8^(b-1)) * ((a+1)!*(b+1)!) := by
      unfold paid unpaid
      rw [Nat.factorial_succ, Nat.factorial_succ]
      ring
    _ ≤ 4 * (8^(a-1)*8^(b-1)) * (2*(a+b)!) := Nat.mul_le_mul_left _ hf
    _ = unpaid (a+b) := by
      unfold unpaid
      rw [← hp]
      ring

/-- Collapse any nonempty list to a paid component without decreasing its
capacity. At two or more children, the new component is actually unpaid. -/
theorem paid_list_le_paid (sizes : List ℕ) (hpos : ∀ m ∈ sizes, 1 ≤ m)
    (hne : sizes ≠ []) : (sizes.map paid).prod ≤ paid sizes.sum := by
  induction sizes with
  | nil => exact (hne rfl).elim
  | cons a sizes ih =>
    cases sizes with
    | nil => simp
    | cons b rest =>
      have ha : 1 ≤ a := hpos a (by simp)
      have htail : ∀ m ∈ b::rest, 1 ≤ m := fun m hm => hpos m (by simp [hm])
      have hb : 1 ≤ (b::rest).sum := by
        have := htail b (by simp)
        simp only [List.sum_cons]
        omega
      calc
        ((a::b::rest).map paid).prod = paid a * ((b::rest).map paid).prod := by simp
        _ ≤ paid a * paid (b::rest).sum := Nat.mul_le_mul_left _ (ih htail (by simp))
        _ ≤ unpaid (a+(b::rest).sum) := paid_pair_le_unpaid ha hb
        _ ≤ paid (a+(b::rest).sum) := unpaid_le_paid _

theorem paid_list_le_unpaid (sizes : List ℕ) (hpos : ∀ m ∈ sizes, 1 ≤ m)
    (hlen : 2 ≤ sizes.length) : (sizes.map paid).prod ≤ unpaid sizes.sum := by
  cases sizes with
  | nil => simp at hlen
  | cons a rest =>
    have ha := hpos a (by simp)
    have hr : rest ≠ [] := by intro h; simp [h] at hlen
    have hrest : ∀ m ∈ rest, 1 ≤ m := fun m hm => hpos m (by simp [hm])
    have hsum : 1 ≤ rest.sum := by
      cases rest with
      | nil => contradiction
      | cons b l =>
        have hb := hrest b (by simp)
        simp only [List.sum_cons]
        omega
    calc
      ((a::rest).map paid).prod = paid a * (rest.map paid).prod := by simp
      _ ≤ paid a * paid rest.sum := Nat.mul_le_mul_left _ (paid_list_le_paid rest hrest hr)
      _ ≤ unpaid (a+rest.sum) := paid_pair_le_unpaid ha hsum

/-- Same dyadic bucket, expressed directly through powers of two. -/
theorem same_bucket_lt_twice {u v b : ℕ}
    (hu : 2^b ≤ u) (hv : v < 2^(b+1)) : v < 2*u := by
  rw [pow_succ] at hv
  nlinarith

/-- The entire group, including the unused survivor, fits the new paid
factor. No equal-package-size hypothesis is required. -/
theorem group_sum_le {d b survivor : ℕ} (weights : List ℕ)
    (hlen : weights.length = d+1)
    (hs : 2^b ≤ survivor)
    (hw : ∀ w ∈ weights, w < 2^(b+1)) :
    weights.sum ≤ 2*(d+1)*survivor := by
  have hbound : ∀ l : List ℕ, (∀ w ∈ l, w ≤ 2*survivor) → l.sum ≤ l.length*(2*survivor) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      have ha := h a (by simp)
      have hl := ih (fun w hw => h w (by simp [hw]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith
  have h := hbound weights (fun w hm => (same_bucket_lt_twice hs (hw w hm)).le)
  rw [hlen] at h
  nlinarith

theorem group_capacity {d b survivor rest : ℕ} (weights : List ℕ)
    (hlen : weights.length = d+1) (hs : 2^b ≤ survivor)
    (hw : ∀ w ∈ weights, w < 2^(b+1))
    (hcap : survivor ≤ unpaid d * rest) :
    weights.sum ≤ paid d * rest := by
  calc
    _ ≤ 2*(d+1)*survivor := group_sum_le weights hlen hs hw
    _ ≤ 2*(d+1)*(unpaid d*rest) := Nat.mul_le_mul_left _ hcap
    _ = paid d * rest := by unfold paid; ring

/-- A polynomial number of dyadic buckets suffices: this deliberately loose
bound avoids real logarithms in the concrete integer scheduler. -/
theorem unpaid_le_power {n : ℕ} (hn : 1 ≤ n) : unpaid n ≤ 2^(4*n^2) := by
  have hnpow : n ≤ 2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hf := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnpow n)
  calc
    unpaid n ≤ 8^n * (2^n)^n := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) hf
    _ = 2^(3*n+n^2) := by rw [show (8:ℕ)=2^3 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ 2^(4*n^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)

end EnvyFreeResearch.Full.RefinedChoresBucketCapacity

#print axioms EnvyFreeResearch.Full.RefinedChoresBucketCapacity.paid_list_le_unpaid
#print axioms EnvyFreeResearch.Full.RefinedChoresBucketCapacity.group_capacity
