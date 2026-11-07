import Mathlib

/-!+# Finite certificates for adaptive chore scheduling

This module checks the gap/mask encodings, scarce-fiber bound, doubling and
finite incidence counts, and the actual floor-reserve arithmetic. It does not
construct measure-valued snapshots, prove physical compensation, or implement
the graph scheduler. Its charging hypotheses are supplied by that separate
finite graph proof; no full oracle protocol is claimed here.
-/

namespace EnvyFreeResearch.R5ChoreSchedule

open scoped BigOperators

abbrev GapPattern (n : ℕ) := Fin n → Fin n → Bool
abbrev LargeClass (n : ℕ) := Fin n × (Fin n → Bool)

theorem card_gap_pattern (n : ℕ) :
    Fintype.card (GapPattern n) = 2 ^ (n * n) := by
  simp [GapPattern, ← pow_mul]

theorem card_large_class (n : ℕ) :
    Fintype.card (LargeClass n) = n * 2 ^ n := by
  simp [LargeClass]

/-- The actual finite-class extraction uses `(S-1)T+1`, not the weaker ST bound. -/
theorem gap_class_extraction {Root : Type*} [Fintype Root] (n S : ℕ)
    (code : Root → GapPattern n) (hS : 0 < S)
    (hpool : (S - 1) * 2 ^ (n * n) < Fintype.card Root) :
    ∃ c, S ≤ (Finset.univ.filter (fun s => code s = c)).card := by
  classical
  have h : Fintype.card (GapPattern n) * (S - 1) < Fintype.card Root := by
    rw [card_gap_pattern]
    simpa [Nat.mul_comm] using hpool
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card code h
  exact ⟨c, by omega⟩

/-- If no mask/next-owner class contains K+1 roots, at most n*2^n*K roots exist. -/
theorem scarce_large_roots {Root : Type*} [Fintype Root] (n K : ℕ)
    (code : Root → LargeClass n)
    (hfiber : ∀ c, (Finset.univ.filter (fun s => code s = c)).card ≤ K) :
    Fintype.card Root ≤ n * 2 ^ n * K := by
  classical
  by_contra h
  have hlt : Fintype.card (LargeClass n) * K < Fintype.card Root := by
    simpa [card_large_class] using (Nat.lt_of_not_ge h)
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card code hlt
  exact (not_lt_of_ge (hfiber c)) hc

theorem scarce_large_envelope (n K count : ℕ)
    (hK : K ≤ n) (hcount : count ≤ n * 2 ^ n * K) :
    count ≤ n * n * 2 ^ n := by
  have h := Nat.mul_le_mul_left (n * 2 ^ n) hK
  calc
    count ≤ n * 2 ^ n * K := hcount
    _ ≤ n * 2 ^ n * n := h
    _ = n * n * 2 ^ n := by ring

theorem next_owner_cohort {Root : Type*} [Fintype Root] (n : ℕ) (hn : 0 < n)
    (next : Root → Fin n) :
    ∃ q, Fintype.card Root / n ≤ (Finset.univ.filter (fun s => next s = q)).card := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply Fintype.exists_le_card_fiber_of_mul_le_card
  simpa using (Nat.mul_div_le (Fintype.card Root) n)

/-- A representative visits each other component member at most once before
its last external advancement; map that last advancement to its own label. -/
theorem representative_lifetime_bound {Agent : Type*} [DecidableEq Agent]
    (component prior : Finset Agent) (owner : Agent) (advances : ℕ)
    (howner : owner ∈ component) (hprior : prior ⊆ component.erase owner)
    (hadvances : advances ≤ prior.card + 1) : advances ≤ component.card := by
  have hcard := Finset.card_le_card hprior
  have herase := Finset.card_erase_add_one howner
  omega

/-- Repeated genuine doubling forces an exponential population requirement. -/
theorem doubling_population (size : ℕ → ℕ) (k : ℕ)
    (hstart : 1 ≤ size 0) (hgrowth : ∀ j < k, 2 * size j ≤ size (j+1)) :
    2 ^ k ≤ size k := by
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hbefore := ih (fun j hj => hgrowth j (by omega))
      have hlast := hgrowth k (by omega)
      rw [pow_succ]
      nlinarith

/-- A single agent's light-child charges are bounded by any binary ceiling. -/
theorem light_charge_count (size : ℕ → ℕ) (k n ell : ℕ)
    (hstart : 1 ≤ size 0) (hgrowth : ∀ j < k, 2 * size j ≤ size (j+1))
    (hcap : size k ≤ n) (hceiling : n ≤ 2 ^ ell) : k ≤ ell := by
  have h := (doubling_population size k hstart hgrowth).trans (hcap.trans hceiling)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h

/-- The component charge sum is exactly the sum of per-agent incidence counts. -/
theorem charge_double_count {Event Agent : Type*} [Fintype Agent]
    [DecidableEq Event] [DecidableEq Agent]
    (events : Finset Event) (component : Event → Finset Agent) :
    (∑ e ∈ events, (component e).card) =
      ∑ a : Agent, (events.filter (fun e => a ∈ component e)).card := by
  classical
  calc
    (∑ e ∈ events, (component e).card) =
        ∑ e ∈ events, ∑ a : Agent, if a ∈ component e then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.card_eq_sum_ite (Finset.subset_univ _)
    _ = ∑ a : Agent, ∑ e ∈ events, if a ∈ component e then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = _ := by simp

/-- Applying the actual per-agent cap to the incidence identity. -/
theorem light_charge_total {Event Agent : Type*} [Fintype Agent]
    [DecidableEq Event] [DecidableEq Agent]
    (events : Finset Event) (component : Event → Finset Agent) (ell : ℕ)
    (hcharge : ∀ a, (events.filter (fun e => a ∈ component e)).card ≤ ell) :
    (∑ e ∈ events, (component e).card) ≤ Fintype.card Agent * ell := by
  rw [charge_double_count]
  calc
    (∑ a : Agent, (events.filter (fun e => a ∈ component e)).card) ≤
        ∑ _a : Agent, ell := Finset.sum_le_sum (fun a _ => hcharge a)
    _ = Fintype.card Agent * ell := by simp

/-- Pairwise-disjoint entering sets are the pivot exception to heavy-child choice. -/
theorem disjoint_charge_total {Event Agent : Type*} [Fintype Agent]
    [DecidableEq Event] [DecidableEq Agent]
    (events : Finset Event) (component : Event → Finset Agent)
    (hdisjoint : ∀ e ∈ events, ∀ f ∈ events, e ≠ f → Disjoint (component e) (component f)) :
    (∑ e ∈ events, (component e).card) ≤ Fintype.card Agent := by
  apply (light_charge_total events component 1 ?_).trans (by simp)
  intro a
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  have hem := Finset.mem_filter.mp he
  have hfm := Finset.mem_filter.mp hf
  exact (Finset.disjoint_left.mp (hdisjoint e hem.1 f hfm.1 hne)) hem.2 hfm.2

theorem total_advances (n ell advances light pivot survivors : ℕ)
    (ha : advances ≤ light + pivot + survivors)
    (hl : light ≤ n * ell) (hp : pivot ≤ n) (hs : survivors ≤ n) :
    advances ≤ n * (ell + 2) := by nlinarith

/-- An explicit injection of consumed revelations into advancements plus a
finite unconsumed set proves the F<=A+n accounting. -/
theorem revelations_bound (filters consumed pending advances n : ℕ)
    (hpartition : filters = consumed + pending)
    (hconsumed : consumed ≤ advances) (hpending : pending ≤ n) :
    filters ≤ advances + n := by omega

theorem total_exponent_charge (n ell advances filters : ℕ)
    (hadvances : advances ≤ n * (ell + 2))
    (hfilters : filters ≤ advances + n) :
    filters + 2 * advances ≤ n * (3 * ell + 7) := by nlinarith

/-- Integer Bernoulli, used to pay a simultaneous d²+1 merger. -/
theorem linear_le_power (n r : ℕ) : 1 + r * n ≤ (n+1)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      calc
        1 + (r+1)*n ≤ (1+r*n)*(n+1) := by nlinarith [Nat.zero_le (r*n*n)]
        _ ≤ (n+1)^r*(n+1) := Nat.mul_le_mul_right (n+1) ih

theorem merger_exponent_bound (n r d : ℕ) (hd : d ≤ r * n) :
    d * d + 1 ≤ (n+1)^(2*r) := by
  have hlinear := linear_le_power n r
  have hsq : (d+1)*(d+1) ≤ ((n+1)^r)*((n+1)^r) := by
    nlinarith
  calc
    d*d+1 ≤ (d+1)*(d+1) := by nlinarith
    _ ≤ ((n+1)^r)*((n+1)^r) := hsq
    _ = (n+1)^(2*r) := by rw [← pow_add]; congr 1; omega

/-- This is the actual subtract-then-pigeonhole floor operation. -/
theorem filter_floor (n B reserve pool : ℕ) (hn : 0 < n)
    (hreserve : B ≤ reserve) (hpool : (n+1)*reserve ≤ pool) :
    reserve ≤ (pool-B)/n := by
  apply (Nat.le_div_iff_mul_le hn).mpr
  have h : reserve*n+B ≤ pool := by nlinarith
  exact Nat.le_sub_of_add_le h

def reserve (n B t : ℕ) : ℕ := (B+n*n+1)*(n+1)^t

theorem reserve_ge_bad (n B t : ℕ) : B ≤ reserve n B t := by
  have hp : 1 ≤ (n+1)^t := one_le_pow₀ (by omega)
  unfold reserve
  nlinarith

theorem reserve_filter_step (n B t pool : ℕ) (hn : 0 < n)
    (hpool : reserve n B (t+1) ≤ pool) :
    reserve n B t ≤ (pool-B)/n := by
  apply filter_floor n B (reserve n B t) pool hn (reserve_ge_bad n B t)
  simpa [reserve, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpool

theorem reserve_merge_step (n B t r group pool : ℕ) (hgroup : 0 < group)
    (hbound : group ≤ (n+1)^(2*r))
    (hpool : reserve n B (t+2*r) ≤ pool) :
    reserve n B t ≤ pool/group := by
  apply (Nat.le_div_iff_mul_le hgroup).mpr
  calc
    reserve n B t * group ≤ reserve n B t * (n+1)^(2*r) :=
      Nat.mul_le_mul_left _ hbound
    _ = reserve n B (t+2*r) := by simp only [reserve, pow_add]; ring
    _ ≤ pool := hpool

inductive PoolOp where
  | filter
  | merge (advances group : ℕ)

def PoolOp.charge : PoolOp → ℕ
  | .filter => 1
  | .merge r _ => 2*r

def PoolOp.valid (n : ℕ) : PoolOp → Prop
  | .filter => True
  | .merge r group => 0 < group ∧ group ≤ (n+1)^(2*r)

def PoolOp.run (n B : ℕ) : PoolOp → ℕ → ℕ
  | .filter, pool => (pool-B)/n
  | .merge _ group, pool => pool/group

def runPool (n B : ℕ) : List PoolOp → ℕ → ℕ
  | [], pool => pool
  | op::ops, pool => runPool n B ops (op.run n B pool)

def totalCharge (ops : List PoolOp) : ℕ := (ops.map PoolOp.charge).sum

/-- Induction over the actual subtract/floor and merge/floor operations: every
legal interleaving spends only its explicitly charged exponent budget. -/
theorem full_pool_budget (n B t : ℕ) (hn : 0 < n) (ops : List PoolOp)
    (hvalid : ∀ op ∈ ops, op.valid n) (pool : ℕ)
    (hpool : reserve n B (totalCharge ops+t) ≤ pool) :
    reserve n B t ≤ runPool n B ops pool := by
  induction ops generalizing pool with
  | nil => simpa [runPool, totalCharge] using hpool
  | cons op ops ih =>
      have htail : ∀ x ∈ ops, x.valid n := by
        intro x hx
        exact hvalid x (by simp [hx])
      have hop := hvalid op (by simp)
      apply ih htail
      cases op with
      | filter =>
          apply reserve_filter_step n B (totalCharge ops+t) pool hn
          simpa [totalCharge, PoolOp.charge, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hpool
      | merge r group =>
          apply reserve_merge_step n B (totalCharge ops+t) r group pool hop.1 hop.2
          simpa [totalCharge, PoolOp.charge, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hpool

end EnvyFreeResearch.R5ChoreSchedule
