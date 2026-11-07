import EnvyFreeResearch.R3Refinement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-!
# Finite balanced-sampling and affine-line certificates

The definitions below use actual integer tickets and finite midpoint grids.
The proofs do not assume a sampler success theorem, LP implementation, oracle
root theorem, or probabilistic waiting-time theorem as an axiom.
-/

namespace EnvyFreeResearch.R4Refinement

open scoped BigOperators

section Tickets

variable {Row : Type*} [Fintype Row] [DecidableEq Row]

noncomputable def floorTickets (B : ℕ) (p : Row → ℝ) (i : Row) : ℕ :=
  ⌊(B : ℝ) * p i⌋₊

/-- All tickets left after the other rows' floors go to one designated recipient.
This is equivalent to flooring every row and giving that recipient the leftovers. -/
noncomputable def roundedTickets (B : ℕ) (p : Row → ℝ) (recipient i : Row) : ℕ :=
  if i = recipient then B - ∑ a ∈ Finset.univ.erase recipient, floorTickets B p a
  else floorTickets B p i

noncomputable def roundedProbability (B : ℕ) (p : Row → ℝ) (recipient i : Row) : ℝ :=
  (roundedTickets B p recipient i : ℝ) / B

omit [DecidableEq Row] in
theorem floor_ticket_sum_le (B : ℕ) (p : Row → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, floorTickets B p i) ≤ B := by
  have hreal : (∑ i, (floorTickets B p i : ℝ)) ≤ B := by
    calc
      (∑ i, (floorTickets B p i : ℝ)) ≤ ∑ i, (B : ℝ) * p i := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg B) (hp i))
      _ = B := by rw [← Finset.mul_sum, hsum, mul_one]
  exact_mod_cast hreal

theorem other_floor_ticket_sum_le (B : ℕ) (p : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ a ∈ Finset.univ.erase recipient, floorTickets B p a) ≤ B := by
  apply le_trans _ (floor_ticket_sum_le B p hp hsum)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => Nat.zero_le _)

theorem recipient_tickets_eq_floor_plus_leftover (B : ℕ) (p : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    roundedTickets B p recipient recipient = floorTickets B p recipient +
      (B - ∑ i, floorTickets B p i) := by
  have hbound := floor_ticket_sum_le B p hp hsum
  have hsplit := Finset.sum_erase_add Finset.univ (floorTickets B p) (Finset.mem_univ recipient)
  simp only [roundedTickets, ite_true]
  omega

theorem rounded_ticket_sum (B : ℕ) (p : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, roundedTickets B p recipient i) = B := by
  have hbound := other_floor_ticket_sum_le B p recipient hp hsum
  calc
    (∑ i, roundedTickets B p recipient i) =
        (∑ i ∈ Finset.univ.erase recipient, floorTickets B p i) +
        (B - ∑ i ∈ Finset.univ.erase recipient, floorTickets B p i) := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ recipient)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [roundedTickets, ite_eq_right (Finset.mem_erase.mp hi).1]
      · simp [roundedTickets]
    _ = B := Nat.add_sub_of_le hbound

theorem rounded_probability_nonneg (B : ℕ) (p : Row → ℝ) (recipient i : Row) :
    0 ≤ roundedProbability B p recipient i := by
  unfold roundedProbability
  positivity

theorem rounded_probability_sum (B : ℕ) (hB : 0 < B) (p : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, roundedProbability B p recipient i) = 1 := by
  simp only [roundedProbability, ← Finset.sum_div, ← Nat.cast_sum,
    rounded_ticket_sum B p recipient hp hsum]
  exact div_self (by exact_mod_cast hB.ne')

theorem zero_row_has_no_tickets (B : ℕ) (p : Row → ℝ) (recipient i : Row)
    (hrecipient : 0 < p recipient) (hi : p i = 0) : roundedTickets B p recipient i = 0 := by
  have hne : i ≠ recipient := by intro h; subst i; linarith
  simp [roundedTickets, hne, floorTickets, hi]

theorem other_probability_deficit (B : ℕ) (hB : 0 < B) (p : Row → ℝ)
    (recipient i : Row) (hp : 0 ≤ p i) (hi : i ≠ recipient) :
    0 ≤ p i - roundedProbability B p recipient i ∧
      p i - roundedProbability B p recipient i < 1 / (B : ℝ) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hlo := Nat.floor_le (mul_nonneg hBreal.le hp)
  have hhi := Nat.lt_floor_add_one ((B : ℝ) * p i)
  have hq : roundedProbability B p recipient i * B = (floorTickets B p i : ℝ) := by
    simp only [roundedProbability, roundedTickets, ite_eq_right hi]
    exact div_mul_cancel₀ _ hBreal.ne'
  have hinv : (1 / (B : ℝ)) * B = 1 := div_mul_cancel₀ _ hBreal.ne'
  change (floorTickets B p i : ℝ) ≤ (B : ℝ) * p i at hlo
  change (B : ℝ) * p i < (floorTickets B p i : ℝ) + 1 at hhi
  constructor
  · apply (mul_le_mul_iff_right₀ hBreal).mp
    nlinarith
  · apply (mul_lt_mul_iff_right₀ hBreal).mp
    nlinarith

/-- Half the L1 discrepancy is exactly the total deficit on all nonrecipient rows. -/
theorem rounded_probability_tv_identity (B : ℕ) (hB : 0 < B) (p : Row → ℝ)
    (recipient : Row) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, |roundedProbability B p recipient i - p i|) / 2 =
      ∑ i ∈ Finset.univ.erase recipient, (p i - roundedProbability B p recipient i) := by
  let q := roundedProbability B p recipient
  let D := ∑ i ∈ Finset.univ.erase recipient, (p i - q i)
  have hdeficit : ∀ i ∈ Finset.univ.erase recipient, 0 ≤ p i - q i := by
    intro i hi
    exact (other_probability_deficit B hB p recipient i (hp i) (Finset.mem_erase.mp hi).1).1
  have hD : 0 ≤ D := Finset.sum_nonneg hdeficit
  have hqsum : ∑ i, q i = 1 := rounded_probability_sum B hB p recipient hp hsum
  have hqsplit := Finset.sum_erase_add Finset.univ q (Finset.mem_univ recipient)
  have hpsplit := Finset.sum_erase_add Finset.univ p (Finset.mem_univ recipient)
  have hrecipient : q recipient - p recipient = D := by
    dsimp [D]
    rw [Finset.sum_sub_distrib]
    linarith
  have hoff : (∑ i ∈ Finset.univ.erase recipient, |q i - p i|) = D := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonpos (by linarith [hdeficit i hi])]
    ring
  have hall : (∑ i, |q i - p i|) = 2 * D := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ recipient),
      hoff, hrecipient, abs_of_nonneg hD]
    ring
  change (∑ i, |q i - p i|) / 2 = D
  rw [hall]
  ring

theorem rounded_probability_tv_bound (B : ℕ) (hB : 0 < B) (p : Row → ℝ)
    (recipient : Row) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, |roundedProbability B p recipient i - p i|) / 2 ≤
      ((Finset.univ.erase recipient).card : ℝ) / B := by
  rw [rounded_probability_tv_identity B hB p recipient hp hsum]
  calc
    (∑ i ∈ Finset.univ.erase recipient, (p i - roundedProbability B p recipient i)) ≤
        ∑ _i ∈ Finset.univ.erase recipient, (1 / (B : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (other_probability_deficit B hB p recipient i (hp i)
        (Finset.mem_erase.mp hi).1).2.le
    _ = ((Finset.univ.erase recipient).card : ℝ) / B := by simp [div_eq_mul_inv]

theorem eight_tickets_per_row_tv (p : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, |roundedProbability (8 * Fintype.card Row) p recipient i - p i|) / 2 <
      (1 / 8 : ℝ) := by
  have hr : 0 < Fintype.card Row := Fintype.card_pos_iff.mpr ⟨recipient⟩
  have hrreal : 0 < (Fintype.card Row : ℝ) := by exact_mod_cast hr
  have hB : 0 < 8 * Fintype.card Row := Nat.mul_pos (by decide) hr
  apply lt_of_le_of_lt (rounded_probability_tv_bound _ hB p recipient hp hsum)
  have hcard : (Finset.univ.erase recipient).card < Fintype.card Row := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ recipient), Finset.card_univ]
    omega
  have hcardreal : ((Finset.univ.erase recipient).card : ℝ) < Fintype.card Row :=
    by exact_mod_cast hcard
  apply (div_lt_iff₀ (show (0 : ℝ) < (8 * Fintype.card Row : ℕ) by positivity)).mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

end Tickets

/-- The [0,1]-test-function characterization needed here is derived from finite
L1 discrepancy by centering at 1/2; it is not assumed as a probability theorem. -/
theorem finite_weighted_tv_bound {Row : Type*} [Fintype Row]
    (p q α : Row → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1) :
    |(∑ i, q i * α i) - (∑ i, p i * α i)| ≤ (∑ i, |q i - p i|) / 2 := by
  have hcenter : (∑ i, q i * α i) - (∑ i, p i * α i) =
      ∑ i, (q i - p i) * (α i - 1 / 2) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, hq]
    ring
  rw [hcenter]
  calc
    |∑ i, (q i - p i) * (α i - 1 / 2)| ≤
        ∑ i, |(q i - p i) * (α i - 1 / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |q i - p i| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith [(hα i).1, (hα i).2]
    _ = (∑ i, |q i - p i|) / 2 := by rw [← Finset.sum_mul]; ring

noncomputable def midpoint {n : ℕ} (i : Fin n) : ℝ :=
  ((i.val : ℝ) + 1 / 2) / n

noncomputable def midpointGood (n : ℕ) (u v : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u < midpoint i ∧ midpoint i < v)

theorem midpoint_monotone (n : ℕ) : Monotone (@midpoint n) := by
  intro i j hij
  unfold midpoint
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hv : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
  linarith

/-- The strict lower CDF includes no target exactly at the interval endpoint. -/
theorem midpoint_strict_cdf_lower (n : ℕ) (hn : 0 < n) (v : ℝ) (hv : v ≤ 1) :
    (n : ℝ) * v - 1 / 2 ≤
      ((Finset.univ.filter (fun i : Fin n => midpoint i < v)).card : ℝ) := by
  let count := (Finset.univ.filter (fun i : Fin n => midpoint i < v)).card
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcount : count ≤ n := by
    simpa [count] using Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i => midpoint i < v)
  change (n : ℝ) * v - 1 / 2 ≤ (count : ℝ)
  by_cases heq : count = n
  · rw [heq]
    nlinarith
  · have hlt : count < n := by omega
    let j : Fin n := ⟨count, hlt⟩
    have hnot : ¬ midpoint j < v := by
      intro hbad
      have hcard := (Fin.lt_card_filter_univ_iff_apply_of_imp
        (j := j) (fun i : Fin n => midpoint i < v)
        (fun i j hji hi => (midpoint_monotone n hji).trans_lt hi)).mpr hbad
      change count < count at hcard
      omega
    have hvbound : v * n ≤ (count : ℝ) + 1 / 2 := by
      apply (le_div_iff₀ hnreal).mp
      exact le_of_not_gt hnot
    nlinarith

theorem midpoint_closed_cdf_upper (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter (fun i : Fin n => midpoint i ≤ u)).card : ℝ) ≤
      (n : ℝ) * u + 1 / 2 := by
  let count := (Finset.univ.filter (fun i : Fin n => midpoint i ≤ u)).card
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcount : count ≤ n := by
    simpa [count] using Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i => midpoint i ≤ u)
  change (count : ℝ) ≤ (n : ℝ) * u + 1 / 2
  by_cases hzero : count = 0
  · rw [hzero]
    norm_num only [Nat.cast_zero]
    nlinarith
  · have hjlt : count - 1 < n := by omega
    let j : Fin n := ⟨count - 1, hjlt⟩
    have hj : midpoint j ≤ u := by
      apply (Fin.lt_card_filter_univ_iff_apply_of_imp
        (j := j) (fun i : Fin n => midpoint i ≤ u)
        (fun i j hji hi => (midpoint_monotone n hji).trans hi)).mp
      change count - 1 < count
      omega
    have hbound : ((count - 1 : ℕ) : ℝ) + 1 / 2 ≤ u * n :=
      (div_le_iff₀ hnreal).mp hj
    have hcast : ((count - 1 : ℕ) : ℝ) + 1 = (count : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ count by omega)
    nlinarith

/-- An actual finite open-interval count for any positive midpoint grid size.
The lower endpoint is excluded using the closed CDF; the upper using the strict CDF. -/
theorem midpoint_open_interval_count (n : ℕ) (hn : 0 < n) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) :
    v - u - 1 / (n : ℝ) ≤ ((midpointGood n u v).card : ℝ) / n := by
  let below := Finset.univ.filter (fun i : Fin n => midpoint i < v)
  let upto := Finset.univ.filter (fun i : Fin n => midpoint i ≤ u)
  have hgood : midpointGood n u v = below \ upto := by
    ext i
    simp only [midpointGood, below, upto, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, not_le]
    exact and_comm
  have hcount : below.card ≤ (midpointGood n u v).card + upto.card := by
    rw [hgood]
    exact Finset.card_le_card_sdiff_add_card
  have hcountreal : (below.card : ℝ) ≤ (midpointGood n u v).card + (upto.card : ℝ) :=
    by exact_mod_cast hcount
  have hlo := midpoint_strict_cdf_lower n hn v hv
  have hhi := midpoint_closed_cdf_upper n hn u hu
  change (n : ℝ) * v - 1 / 2 ≤ (below.card : ℝ) at hlo
  change (upto.card : ℝ) ≤ (n : ℝ) * u + 1 / 2 at hhi
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hinv : (1 / (n : ℝ)) * n = 1 := div_mul_cancel₀ _ hnreal.ne'
  apply (le_div_iff₀ hnreal).mpr
  nlinarith

/-- Guaranteed mass of good ticket/midpoint pairs is at least 1/4. This is a
finite counting statement; geometric legal-root and conditional sampling arguments
must separately show that these pairs are indeed accepted by the oracle algorithm. -/
theorem finite_sampler_guaranteed_mass {Row : Type*} [Fintype Row] [DecidableEq Row]
    (p u v : Row → ℝ) (recipient : Row)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hinterval : ∀ i, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ 1)
    (hwidth : ∑ i, p i * (v i - u i) = 1 / 2) :
    (1 / 4 : ℝ) ≤ ∑ i, roundedProbability (8 * Fintype.card Row) p recipient i *
      (((midpointGood 8 (u i) (v i)).card : ℝ) / 8) := by
  let q := roundedProbability (8 * Fintype.card Row) p recipient
  let α := fun i => v i - u i
  let good := fun i => ((midpointGood 8 (u i) (v i)).card : ℝ) / 8
  have hr : 0 < Fintype.card Row := Fintype.card_pos_iff.mpr ⟨recipient⟩
  have hqsum : ∑ i, q i = 1 :=
    rounded_probability_sum _ (by omega) p recipient hp hsum
  have hqnonneg : ∀ i, 0 ≤ q i := rounded_probability_nonneg _ p recipient
  have hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 := by
    intro i
    dsimp [α]
    have h := hinterval i
    constructor <;> linarith
  have htv := finite_weighted_tv_bound p q α hsum hqsum hα
  have htvsmall := eight_tickets_per_row_tv p recipient hp hsum
  have hwidth' : ∑ i, p i * α i = 1 / 2 := hwidth
  have hαlower : (3 / 8 : ℝ) ≤ ∑ i, q i * α i := by
    have h := (abs_le.mp htv).1
    change (∑ i, |q i - p i|) / 2 < 1 / 8 at htvsmall
    linarith
  have hgood : ∀ i, α i - 1 / 8 ≤ good i := by
    intro i
    exact midpoint_open_interval_count 8 (by decide) (u i) (v i)
      (hinterval i).1 (hinterval i).2.2
  have hweighted : (∑ i, q i * α i) - 1 / 8 ≤ ∑ i, q i * good i := by
    calc
      (∑ i, q i * α i) - 1 / 8 = ∑ i, q i * (α i - 1 / 8) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hqsum, one_mul]
      _ ≤ ∑ i, q i * good i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hgood i) (hqnonneg i)
  change (1 / 4 : ℝ) ≤ ∑ i, q i * good i
  linarith

/-- An accepted aggregate prefix leaves both children within the 3/4 budget. -/
theorem balanced_children (total prefixMass : ℝ)
    (hlower : total / 4 ≤ prefixMass) (hupper : prefixMass ≤ 3 * total / 4) :
    prefixMass ≤ (3 / 4) * total ∧ total - prefixMass ≤ (3 / 4) * total := by
  constructor <;> linarith

/-- The exact finite ancestry invariant along J accepted balanced splits. -/
theorem aggregate_path_contraction (mass : ℕ → ℝ) (initial : ℝ) (J : ℕ)
    (hstart : mass 0 ≤ initial)
    (hstep : ∀ j < J, mass (j + 1) ≤ (3 / 4) * mass j) :
    mass J ≤ initial * (3 / 4) ^ J := by
  induction J with
  | zero => simpa using hstart
  | succ J ih =>
      have hprev := ih (fun j hj => hstep j (by omega))
      calc
        mass (J + 1) ≤ (3 / 4) * mass J := hstep J (by omega)
        _ ≤ (3 / 4) * (initial * (3 / 4) ^ J) :=
          mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ = initial * (3 / 4) ^ (J + 1) := by rw [pow_succ]; ring

theorem sparse_path_mass_bound {Cell : Type*} (fractional : Finset Cell)
    (mass : Cell → ℕ → ℝ) (r : ℝ) (d J : ℕ)
    (hr : 0 ≤ r) (hcount : fractional.card ≤ d)
    (hstart : ∀ c ∈ fractional, mass c 0 ≤ r)
    (hstep : ∀ c ∈ fractional, ∀ j < J, mass c (j + 1) ≤ (3 / 4) * mass c j) :
    (∑ c ∈ fractional, mass c J) ≤ (d : ℝ) * r * (3 / 4) ^ J := by
  have h := R3Refinement.residual_mass_bound fractional (fun c => mass c J)
    (r * (3 / 4) ^ J) d (by positivity) hcount
    (fun c hc => aggregate_path_contraction (mass c) r J (hstart c hc) (hstep c hc))
  simpa only [mul_assoc] using h

/-- This counts accepted split invocations. Rejected candidate queries are not
bounded by it and must be charged separately in the probabilistic runtime proof. -/
theorem split_invocation_ledger (calls : ℕ → ℕ) (d J : ℕ)
    (hcall : ∀ j < J, calls j ≤ d) : (∑ j ∈ Finset.range J, calls j) ≤ d * J := by
  calc
    (∑ j ∈ Finset.range J, calls j) ≤ ∑ _j ∈ Finset.range J, d := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcall j (Finset.mem_range.mp hj)
    _ = d * J := by simp [Nat.mul_comm]

/-- A realized finite run charges every attempted Cut and every observer record. -/
theorem attempted_query_ledger {Attempt : Type*}
    (attempts : Finset Attempt) (queries : Attempt → ℕ) (recorders : ℕ)
    (hquery : ∀ a ∈ attempts, queries a ≤ recorders + 1) :
    (∑ a ∈ attempts, queries a) ≤ attempts.card * (recorders + 1) := by
  calc
    (∑ a ∈ attempts, queries a) ≤ ∑ _a ∈ attempts, (recorders + 1) :=
      Finset.sum_le_sum hquery
    _ = attempts.card * (recorders + 1) := by simp

/-- For a nonzero scalar coefficient, every normalized correction event is
exactly the same scalar event; no union over observers is needed at this algebraic step. -/
theorem scalar_bad_event_iff (c x b D : ℝ) (hc : c ≠ 0) :
    b * (|c| * D) < |c * x| ↔ b * D < |x| := by
  rw [abs_mul]
  have hrewrite : b * (|c| * D) = |c| * (b * D) := by ring
  rw [hrewrite, mul_lt_mul_iff_right₀ (abs_pos.mpr hc)]

theorem zero_coefficient_has_no_bad_event (x b D : ℝ) :
    ¬ b * (|(0 : ℝ)| * D) < |(0 : ℝ) * x| := by simp

theorem affine_pair_difference (base a b direction : ℝ) :
    (base + a * direction) - (base + b * direction) = (a - b) * direction := by ring

/-- Exact reconstruction at an arbitrary second coordinate from one separating
coordinate in a promised affine-line family. The global affine promise is external. -/
theorem affine_coordinate_reconstruction (a lo hi base direction zbase zdirection : ℝ)
    (hsep : (zbase + hi * zdirection) - (zbase + lo * zdirection) ≠ 0) :
    let t := ((zbase + a * zdirection) - (zbase + lo * zdirection)) /
      ((zbase + hi * zdirection) - (zbase + lo * zdirection))
    (1 - t) * (base + lo * direction) + t * (base + hi * direction) =
      base + a * direction := by
  dsimp only
  have hden : (zbase + hi * zdirection) - (zbase + lo * zdirection) =
      zdirection * (hi - lo) := by ring
  have hnum : (zbase + a * zdirection) - (zbase + lo * zdirection) =
      zdirection * (a - lo) := by ring
  have hprod : zdirection * (hi - lo) ≠ 0 := by simpa only [hden] using hsep
  have hz : zdirection ≠ 0 := left_ne_zero_of_mul hprod
  have hd : hi - lo ≠ 0 := right_ne_zero_of_mul hprod
  rw [hnum, hden, mul_div_mul_left _ _ hz]
  field_simp [hd]
  ring

theorem separating_coordinate_coefficient_in_unit (lo x hi : ℝ)
    (hsep : lo < hi) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    0 ≤ (x - lo) / (hi - lo) ∧ (x - lo) / (hi - lo) ≤ 1 := by
  have hden : 0 < hi - lo := sub_pos.mpr hsep
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hden.le
  · apply (div_le_iff₀ hden).mpr
    linarith

theorem convex_denominator_positive (t left right : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (hl : 0 < left) (hr : 0 < right) :
    0 < (1 - t) * left + t * right := by
  by_cases hzero : t = 0
  · simpa [hzero] using hl
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hleft : 0 ≤ (1 - t) * left := mul_nonneg (by linarith [ht.2]) hl.le
    have hright : 0 < t * right := mul_pos htpos hr
    linarith

noncomputable def normalizedCoefficient (t left right : ℝ) : ℝ :=
  t * right / ((1 - t) * left + t * right)

/-- Positive common-reserve normalization preserves convex coefficients. -/
theorem normalized_coefficient_in_unit (t left right : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (hl : 0 < left) (hr : 0 < right) :
    0 ≤ normalizedCoefficient t left right ∧ normalizedCoefficient t left right ≤ 1 := by
  have hden := convex_denominator_positive t left right ht hl hr
  have hleft : 0 ≤ (1 - t) * left := mul_nonneg (by linarith [ht.2]) hl.le
  constructor
  · exact div_nonneg (mul_nonneg ht.1 hr.le) hden.le
  · unfold normalizedCoefficient
    apply (div_le_iff₀ hden).mpr
    linarith

theorem convex_normalization_identity (t left right valueLeft valueRight : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (hl : 0 < left) (hr : 0 < right) :
    ((1 - t) * valueLeft + t * valueRight) / ((1 - t) * left + t * right) =
      (1 - normalizedCoefficient t left right) * (valueLeft / left) +
      normalizedCoefficient t left right * (valueRight / right) := by
  have hden := convex_denominator_positive t left right ht hl hr
  unfold normalizedCoefficient
  field_simp
  ring

#print axioms rounded_ticket_sum
#print axioms eight_tickets_per_row_tv
#print axioms midpoint_open_interval_count
#print axioms finite_sampler_guaranteed_mass
#print axioms sparse_path_mass_bound
#print axioms scalar_bad_event_iff
#print axioms affine_coordinate_reconstruction
#print axioms convex_normalization_identity

end EnvyFreeResearch.R4Refinement
