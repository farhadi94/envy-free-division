import EnvyFreeResearch.Full.UpperAssignment
import EnvyFreeResearch.Full.UpperSeedProbability
import Mathlib.GroupTheory.Perm.Support

/-!
# Coupling actual assignment improvements to isolation charges

A permutation of owners constructs the competing assignment. Its loss is
nonnegative by the actual finite optimizer, and bounds every transferred
column gap by the deleted-column theorem. A positive augmented cycle then
forces at least one unit of charge, without conditioning on the winning
assignment.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperAssignmentIsolation

open UpperAssignment UpperSeedProbability

/-- If a charge is below its cap, its numerator is at most the common gap
bound times that charge. The zero discrepancy and zero gap branches are
handled by the actual charge convention. -/
theorem coefficient_le_gap_mul_charge (A lam value delta : ℝ)
    (hA : 0 ≤ A) (hlam : 0 ≤ lam) (hgap : |value| ≤ delta)
    (hsmall : charge A lam value < 1) :
    2 * lam * A ≤ delta * charge A lam value := by
  by_cases hzero : A = 0
  · simp [charge, hzero]
  · have hvalue : value ≠ 0 := by
      intro hv
      simp [charge, hzero, hv] at hsmall
    have hratio : 2 * lam * A / |value| < 1 := by
      by_contra hn
      have hle : 1 ≤ 2 * lam * A / |value| := le_of_not_gt hn
      simp [charge, hzero, hvalue, min_eq_left hle] at hsmall
    have hcharge : charge A lam value = 2 * lam * A / |value| := by
      simp [charge, hzero, hvalue, min_eq_right hratio.le]
    have heq : |value| * charge A lam value = 2 * lam * A := by
      rw [hcharge]
      field_simp
    rw [← heq]
    exact mul_le_mul_of_nonneg_right hgap (charge_nonneg A lam value hA hlam)

/-- Any finite collection of gaps bounded by `delta` whose total numerator
exceeds `delta` carries total capped charge at least one. -/
theorem one_le_sum_charge {Index : Type*} (indices : Finset Index)
    (A gap : Index → ℝ) (lam delta : ℝ) (hlam : 0 ≤ lam) (hdelta : 0 ≤ delta)
    (hA : ∀ i ∈ indices, 0 ≤ A i) (hgap : ∀ i ∈ indices, |gap i| ≤ delta)
    (hpositive : delta < ∑ i ∈ indices, 2 * lam * A i) :
    1 ≤ ∑ i ∈ indices, charge (A i) lam (gap i) := by
  by_contra hn
  have hsmall : (∑ i ∈ indices, charge (A i) lam (gap i)) < 1 := lt_of_not_ge hn
  have heach (i : Index) (hi : i ∈ indices) : charge (A i) lam (gap i) < 1 :=
    (Finset.single_le_sum (fun j hj => charge_nonneg (A j) lam (gap j) (hA j hj) hlam) hi).trans_lt hsmall
  have hsum := Finset.sum_le_sum (fun i hi =>
    coefficient_le_gap_mul_charge (A i) lam (gap i) delta (hA i hi) hlam (hgap i hi)
      (heach i hi))
  have hle := mul_le_mul_of_nonneg_left hsmall.le hdelta
  simp only [Finset.mul_sum] at hle
  nlinarith

theorem truncated_sum_lower_bound {Index : Type*} (indices : Finset Index)
    (values : Index → ℝ) (a : ℝ) (hone : 1 ≤ ∑ i ∈ indices, values i) :
    1 - indices.card * a ≤ ∑ i ∈ indices, max (values i - a) 0 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ indices) => le_max_left (values i - a) 0)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def competitor (V : Agent → Agent → ℝ) (transfer : Equiv.Perm Agent) : Equiv.Perm Agent :=
  transfer.trans (maximize V)

def loss (V : Agent → Agent → ℝ) (transfer : Equiv.Perm Agent) : ℝ :=
  score V (maximize V) - score V (competitor V transfer)

def gap (V : Agent → Agent → ℝ) (i owner : Agent) : ℝ :=
  forcedValue V i (maximize V owner) - forcedValue V owner (maximize V owner)

def margin (V A : Agent → Agent → ℝ) (lam : ℝ) (transfer : Equiv.Perm Agent) : ℝ :=
  ∑ i ∈ transfer.support,
    (V i (maximize V (transfer i)) - V i (maximize V i) + 2 * lam * A i (transfer i))

theorem loss_nonnegative (V : Agent → Agent → ℝ) (transfer : Equiv.Perm Agent) :
    0 ≤ loss V transfer := sub_nonneg.mpr (maximize_spec V _)

theorem transferred_gap_le_loss (V : Agent → Agent → ℝ) (transfer : Equiv.Perm Agent)
    (i : Agent) : |gap V i (transfer i)| ≤ loss V transfer :=
  forced_gap_le_loss V i (transfer i) (competitor V transfer) rfl

theorem margin_eq (V A : Agent → Agent → ℝ) (lam : ℝ) (transfer : Equiv.Perm Agent) :
    margin V A lam transfer = -loss V transfer +
      ∑ i ∈ transfer.support, 2 * lam * A i (transfer i) := by
  have hsum : (∑ i ∈ transfer.support,
      (V i (maximize V (transfer i)) - V i (maximize V i))) =
      ∑ i, (V i (maximize V (transfer i)) - V i (maximize V i)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Equiv.Perm.notMem_support.mp hi]
  rw [margin, Finset.sum_add_distrib, hsum, Finset.sum_sub_distrib]
  simp only [loss, score, competitor, Equiv.trans_apply]
  ring

/-- This is the deterministic heart of the cycle argument: the actual
optimal assignment, and any positive augmented permutation of its columns,
produce at least unit total charge along the transferred columns. -/
theorem positive_margin_charge (V A : Agent → Agent → ℝ) (lam : ℝ)
    (transfer : Equiv.Perm Agent) (hA : ∀ i j, 0 ≤ A i j) (hlam : 0 ≤ lam)
    (hpositive : 0 < margin V A lam transfer) :
    1 ≤ ∑ i ∈ transfer.support, charge (A i (transfer i)) lam (gap V i (transfer i)) := by
  apply one_le_sum_charge transfer.support (fun i => A i (transfer i))
    (fun i => gap V i (transfer i)) lam (loss V transfer) hlam (loss_nonnegative V transfer)
    (fun i _ => hA i (transfer i)) (fun i _ => transferred_gap_le_loss V transfer i)
  rw [margin_eq] at hpositive
  linarith

theorem positive_margin_truncated_charge (V A : Agent → Agent → ℝ) (lam a : ℝ)
    (transfer : Equiv.Perm Agent) (hA : ∀ i j, 0 ≤ A i j) (hlam : 0 ≤ lam)
    (ha : 0 ≤ a) (hpositive : 0 < margin V A lam transfer) :
    1 - Fintype.card Agent * a ≤ ∑ i ∈ transfer.support,
      max (charge (A i (transfer i)) lam (gap V i (transfer i)) - a) 0 := by
  have h := truncated_sum_lower_bound transfer.support
    (fun i => charge (A i (transfer i)) lam (gap V i (transfer i))) a
    (positive_margin_charge V A lam transfer hA hlam hpositive)
  have hcard : (transfer.support.card : ℝ) ≤ Fintype.card Agent := by
    exact_mod_cast Finset.card_le_univ transfer.support
  have hm := mul_le_mul_of_nonneg_right hcard ha
  linarith

end EnvyFreeResearch.Full.UpperAssignmentIsolation
