import EnvyFreeResearch.Full.ChoresComponentPopulationTree

/-! Separate scalar query/Cut recurrences for the actual proper-population
recursion. The maxima range over a smaller unary child and two positive
children whose populations sum to the parent. Ambient restoration is charged
only as parent population times child Cuts. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open scoped BigOperators

structure Capacity where
  queries : ℕ
  cuts : ℕ

def capacityStep (localQ localC : ℕ → ℕ) (n : ℕ) (previous : Fin n → Capacity) : Capacity where
  queries := localQ n + max
    (Finset.univ.sup (fun k => (previous k).queries+n*(previous k).cuts))
    (Finset.univ.sup (fun pair : Fin n × Fin n =>
      if 0 < pair.1.val ∧ 0 < pair.2.val ∧ pair.1.val+pair.2.val=n then
        (previous pair.1).queries+(previous pair.2).queries+n*((previous pair.1).cuts+(previous pair.2).cuts)
      else 0))
  cuts := localC n + max
    (Finset.univ.sup (fun k => (previous k).cuts))
    (Finset.univ.sup (fun pair : Fin n × Fin n =>
      if 0 < pair.1.val ∧ 0 < pair.2.val ∧ pair.1.val+pair.2.val=n then
        (previous pair.1).cuts+(previous pair.2).cuts else 0))

def capacity (localQ localC : ℕ → ℕ) (n : ℕ) : Capacity :=
  Nat.strongRecOn n (fun m previous =>
    if m = 0 then ⟨0,0⟩ else capacityStep localQ localC m (fun k => previous k.val k.isLt))

theorem capacity_zero (localQ localC : ℕ → ℕ) : capacity localQ localC 0 = ⟨0,0⟩ := by
  rw [capacity, Nat.strongRecOn_eq]
  simp only [ite_true]

theorem capacity_step (localQ localC : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    capacity localQ localC n = capacityStep localQ localC n (fun k => capacity localQ localC k.val) := by
  rw [capacity, Nat.strongRecOn_eq, ite_eq_right (by omega : n ≠ 0)]
  rfl

theorem capacity_local (localQ localC : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    localQ n ≤ (capacity localQ localC n).queries ∧ localC n ≤ (capacity localQ localC n).cuts := by
  rw [capacity_step localQ localC hn]
  exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem capacity_one (localQ localC : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    localQ n+(capacity localQ localC k).queries+n*(capacity localQ localC k).cuts ≤
        (capacity localQ localC n).queries ∧
      localC n+(capacity localQ localC k).cuts ≤ (capacity localQ localC n).cuts := by
  rw [capacity_step localQ localC (by omega : 0 < n)]
  have hq := Finset.le_sup (f := fun j : Fin n => (capacity localQ localC j.val).queries+n*(capacity localQ localC j.val).cuts)
    (Finset.mem_univ (⟨k,hk⟩ : Fin n))
  have hc := Finset.le_sup (f := fun j : Fin n => (capacity localQ localC j.val).cuts)
    (Finset.mem_univ (⟨k,hk⟩ : Fin n))
  constructor
  · exact (by simpa only [capacityStep, Nat.add_assoc] using Nat.add_le_add_left (hq.trans (le_max_left _ _)) (localQ n))
  · exact Nat.add_le_add_left (hc.trans (le_max_left _ _)) _

theorem capacity_two (localQ localC : ℕ → ℕ) {n b c : ℕ} (hb : 0 < b) (hc : 0 < c) (hsum : b+c=n) :
    localQ n+(capacity localQ localC b).queries+(capacity localQ localC c).queries+
        n*((capacity localQ localC b).cuts+(capacity localQ localC c).cuts) ≤ (capacity localQ localC n).queries ∧
      localC n+(capacity localQ localC b).cuts+(capacity localQ localC c).cuts ≤ (capacity localQ localC n).cuts := by
  have hbn : b < n := by omega
  have hcn : c < n := by omega
  rw [capacity_step localQ localC (by omega : 0 < n)]
  let pair : Fin n × Fin n := (⟨b,hbn⟩,⟨c,hcn⟩)
  have hp : 0 < pair.1.val ∧ 0 < pair.2.val ∧ pair.1.val+pair.2.val=n := ⟨hb,hc,hsum⟩
  have hq := Finset.le_sup (f := fun p : Fin n × Fin n =>
    if 0 < p.1.val ∧ 0 < p.2.val ∧ p.1.val+p.2.val=n then
      (capacity localQ localC p.1.val).queries+(capacity localQ localC p.2.val).queries+
        n*((capacity localQ localC p.1.val).cuts+(capacity localQ localC p.2.val).cuts) else 0)
    (Finset.mem_univ pair)
  have hcut := Finset.le_sup (f := fun p : Fin n × Fin n =>
    if 0 < p.1.val ∧ 0 < p.2.val ∧ p.1.val+p.2.val=n then
      (capacity localQ localC p.1.val).cuts+(capacity localQ localC p.2.val).cuts else 0)
    (Finset.mem_univ pair)
  rw [ite_eq_left hp] at hq hcut
  constructor
  · simpa only [capacityStep, pair, Nat.add_assoc] using Nat.add_le_add_left (hq.trans (le_max_right _ _)) (localQ n)
  · simpa only [capacityStep, pair, Nat.add_assoc] using Nat.add_le_add_left (hcut.trans (le_max_right _ _)) (localC n)

theorem lifted_envelope {k n q c MQ MC : ℕ} (hkn : k < n)
    (hq : q ≤ (2*k-1)*(MQ+k^2*MC)) (hc : c ≤ (2*k-1)*MC) :
    q+n*c ≤ (2*k-1)*(MQ+n^2*MC) := by
  have hs := Tree.square_step hkn
  calc
    q+n*c ≤ (2*k-1)*(MQ+k^2*MC)+n*((2*k-1)*MC) := Nat.add_le_add hq (Nat.mul_le_mul_left n hc)
    _ = (2*k-1)*(MQ+(k^2+n)*MC) := by ring
    _ ≤ (2*k-1)*(MQ+n^2*MC) := Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right MC hs) MQ)

/-- Uniform local bounds give the same 2n-1 node and n² ancestor-recording
envelope as the explicit recursion tree. No inherited query budget is
multiplied by the population size. -/
theorem capacity_envelope (localQ localC : ℕ → ℕ) (n MQ MC : ℕ)
    (hQ : ∀ k, 0 < k → k ≤ n → localQ k ≤ MQ)
    (hC : ∀ k, 0 < k → k ≤ n → localC k ≤ MC) :
    (capacity localQ localC n).queries ≤ (2*n-1)*(MQ+n^2*MC) ∧
      (capacity localQ localC n).cuts ≤ (2*n-1)*MC := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      rw [capacity_zero]
      simp
    · have hn : 0 < n := by omega
      have hprev (k : Fin n) := ih k.val k.isLt
        (fun j hj hjk => hQ j hj (hjk.trans k.isLt.le))
        (fun j hj hjk => hC j hj (hjk.trans k.isLt.le))
      have hqOne : (Finset.univ.sup (fun k : Fin n =>
          (capacity localQ localC k.val).queries+n*(capacity localQ localC k.val).cuts)) ≤
          (2*n-2)*(MQ+n^2*MC) := by
        apply Finset.sup_le
        intro k _
        exact (lifted_envelope k.isLt (hprev k).1 (hprev k).2).trans
          (Nat.mul_le_mul_right _ (by omega : 2*k.val-1 ≤ 2*n-2))
      have hcOne : (Finset.univ.sup (fun k : Fin n => (capacity localQ localC k.val).cuts)) ≤ (2*n-2)*MC := by
        apply Finset.sup_le
        intro k _
        exact (hprev k).2.trans (Nat.mul_le_mul_right MC (by omega : 2*k.val-1 ≤ 2*n-2))
      have hqTwo : (Finset.univ.sup (fun p : Fin n × Fin n =>
          if 0 < p.1.val ∧ 0 < p.2.val ∧ p.1.val+p.2.val=n then
            (capacity localQ localC p.1.val).queries+(capacity localQ localC p.2.val).queries+
              n*((capacity localQ localC p.1.val).cuts+(capacity localQ localC p.2.val).cuts) else 0)) ≤
          (2*n-2)*(MQ+n^2*MC) := by
        apply Finset.sup_le
        intro p _
        split_ifs with hp
        · have hl := lifted_envelope p.1.isLt (hprev p.1).1 (hprev p.1).2
          have hr := lifted_envelope p.2.isLt (hprev p.2).1 (hprev p.2).2
          have hnodes : (2*p.1.val-1)+(2*p.2.val-1)=2*n-2 := by omega
          calc
            _ = ((capacity localQ localC p.1.val).queries+n*(capacity localQ localC p.1.val).cuts)+
                ((capacity localQ localC p.2.val).queries+n*(capacity localQ localC p.2.val).cuts) := by ring
            _ ≤ (2*p.1.val-1)*(MQ+n^2*MC)+(2*p.2.val-1)*(MQ+n^2*MC) := Nat.add_le_add hl hr
            _ = _ := by rw [← Nat.add_mul, hnodes]
        · exact Nat.zero_le _
      have hcTwo : (Finset.univ.sup (fun p : Fin n × Fin n =>
          if 0 < p.1.val ∧ 0 < p.2.val ∧ p.1.val+p.2.val=n then
            (capacity localQ localC p.1.val).cuts+(capacity localQ localC p.2.val).cuts else 0)) ≤ (2*n-2)*MC := by
        apply Finset.sup_le
        intro p _
        split_ifs with hp
        · have hnodes : (2*p.1.val-1)+(2*p.2.val-1)=2*n-2 := by omega
          simpa only [← Nat.add_mul, hnodes] using Nat.add_le_add (hprev p.1).2 (hprev p.2).2
        · exact Nat.zero_le _
      have hlocalQ := hQ n hn le_rfl
      have hlocalC := hC n hn le_rfl
      have hnodes : (2*n-2)+1=2*n-1 := by omega
      rw [capacity_step localQ localC hn]
      constructor
      · change localQ n+max _ _ ≤ _
        calc
          _ ≤ MQ+(2*n-2)*(MQ+n^2*MC) := Nat.add_le_add hlocalQ (max_le hqOne hqTwo)
          _ ≤ (MQ+n^2*MC)+(2*n-2)*(MQ+n^2*MC) := Nat.add_le_add_right (Nat.le_add_right MQ _) _
          _ = _ := by rw [← hnodes]; ring
      · change localC n+max _ _ ≤ _
        calc
          _ ≤ MC+(2*n-2)*MC := Nat.add_le_add hlocalC (max_le hcOne hcTwo)
          _ = _ := by rw [← hnodes]; ring

end EnvyFreeResearch.Full.Chores.Population
