import EnvyFreeResearch.Full.UpperFloating
import EnvyFreeResearch.Full.UpperWholePaymentsPhysical
import EnvyFreeResearch.Full.UpperIdealMeasurable

/-!
# Concrete measurable whole-payment construction

Normalized cached cell rows and nonnegative targets summing to at most one
are the only allocation inputs. The floating and rounding implementations
produce the payments, their deficits, and their disagreement bounds. No
sparse fractional plan or rounded payment is supplied as a premise.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperPayments

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def cellGap (a : Agent → Cell → ℝ) (i j : Agent) : ℝ :=
  if h : (Finset.univ : Finset Cell).Nonempty then
    Finset.univ.sup' h (fun e => |a i e - a j e|) else 0

omit [Fintype Agent] in
theorem cellGap_nonneg (a : Agent → Cell → ℝ) (i j : Agent) : 0 ≤ cellGap a i j := by
  unfold cellGap
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    exact (abs_nonneg (a i e - a j e)).trans (Finset.le_sup' (fun e => |a i e - a j e|) he)
  · exact le_rfl

omit [Fintype Agent] in
theorem difference_le_cellGap (a : Agent → Cell → ℝ) (i j : Agent) (e : Cell) :
    |a i e - a j e| ≤ cellGap a i j := by
  have h : (Finset.univ : Finset Cell).Nonempty := ⟨e, Finset.mem_univ e⟩
  simp only [cellGap, dite_eq_left h]
  exact Finset.le_sup' (fun e => |a i e - a j e|) (Finset.mem_univ e)

omit [Fintype Agent] in
theorem cellGap_le (a : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta) (i j : Agent) :
    cellGap a i j ≤ eta := by
  unfold cellGap
  split_ifs with h
  · apply Finset.sup'_le
    intro e _
    apply abs_le.mpr
    constructor <;> linarith [ha i e, ha j e, hsmall i e, hsmall j e]
  · exact heta

theorem cellGap_diagonal (a : Agent → Cell → ℝ) (i : Agent) : cellGap a i i = 0 := by
  apply le_antisymm _ (cellGap_nonneg a i i)
  unfold cellGap
  split_ifs
  · apply Finset.sup'_le
    intro e _
    simp
  · exact le_rfl

omit [Fintype Agent] in
theorem cellGap_symmetric (a : Agent → Cell → ℝ) (i j : Agent) : cellGap a i j = cellGap a j i := by
  have heq : (fun e => |a i e - a j e|) = (fun e => |a j e - a i e|) :=
    funext (fun e => abs_sub_comm (a i e) (a j e))
  unfold cellGap
  rw [heq]

def allocation (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) : Agent → Finset Cell :=
  UpperWholePayments.owned a (UpperFloating.plan a t) eta

def value (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) (i j : Agent) : ℝ :=
  ∑ e ∈ allocation a t eta j, a i e

def deficit (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) (j : Agent) : ℝ :=
  t j - value a t eta j j

/-- All whole-payment assertions are proved for the actual composite
algorithm, with the cell disagreement computed directly from its cache. -/
theorem allocation_spec (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) :
    (∀ i j, i ≠ j → Disjoint (allocation a t eta i) (allocation a t eta j)) ∧
      (∀ j, 0 ≤ deficit a t eta j ∧ deficit a t eta j ≤ min (t j) eta) ∧
      (∑ j, deficit a t eta j) ≤ Fintype.card Agent * eta ∧
      ∀ i j, |value a t eta i j - value a t eta j j| ≤
        (Fintype.card Agent : ℝ)^2 * cellGap a i j := by
  obtain ⟨hbox, hrow, hmom, _, hcount⟩ := UpperFloating.plan_spec a t hnormal ht hsum
  have hb := UpperWholePayments.whole_payment_bounds a (UpperFloating.plan a t) eta t
    (cellGap a) heta ha hsmall hbox hrow hmom (cellGap_nonneg a)
    (difference_le_cellGap a) hcount
  refine ⟨?_, hb⟩
  exact UpperWholePayments.owned_disjoint a (UpperFloating.plan a t) eta heta ha hsmall hbox hrow

section Measurability

variable {X : Type*} [MeasurableSpace X]

omit [Fintype Agent] in
theorem cellGap_measurable (a : X → Agent → Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (i j : Agent) :
    Measurable (fun z => cellGap (a z) i j) := by
  by_cases h : (Finset.univ : Finset Cell).Nonempty
  · simp only [cellGap, dite_eq_left h]
    have hm := Finset.measurable_sup' h
      (fun e (_ : e ∈ (Finset.univ : Finset Cell)) => ((ha i e).sub (ha j e)).abs)
    convert hm using 1
    funext z
    simp only [Finset.sup'_apply, Pi.sub_apply]
  · simpa only [cellGap, dite_eq_right h] using (measurable_const : Measurable (fun _ : X => (0 : ℝ)))

theorem allocation_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) : Measurable (fun z => allocation (a z) (t z) (eta z)) := by
  have hp := UpperFloating.plan_measurable a t ha ht
  exact UpperWholePaymentsPhysical.owned_measurable a (fun z => UpperFloating.plan (a z) (t z)) eta
    ha (fun e c => (measurable_pi_apply c).comp ((measurable_pi_apply e).comp hp)) heta

theorem value_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) (i j : Agent) : Measurable (fun z => value (a z) (t z) (eta z) i j) := by
  have hp := UpperFloating.plan_measurable a t ha ht
  exact UpperWholePaymentsPhysical.value_measurable a (fun z => UpperFloating.plan (a z) (t z)) eta
    ha (fun e c => (measurable_pi_apply c).comp ((measurable_pi_apply e).comp hp)) heta i j

theorem deficit_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) (j : Agent) : Measurable (fun z => deficit (a z) (t z) (eta z) j) :=
  (ht j).sub (value_measurable a t eta ha ht heta j j)

end Measurability

/-- Cached masses are realized by literal disjoint finite cell unions. -/
theorem physical_spec (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (hcells : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (a : Agent → Cell → ℝ) (hcache : ∀ i e, a i e = (cost i).real (cells e))
    (t : Agent → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ i e, a i e ≤ eta) (hnormal : ∀ i, ∑ e, a i e = 1)
    (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) :
    let Y := UpperWholePaymentsPhysical.piece cells (allocation a t eta)
    (Pairwise (fun i j => Disjoint (Y i) (Y j))) ∧
      (∀ j, MeasurableSet (Y j) ∧ Y j ⊆ ⋃ e, cells e) ∧
      (∀ i j, (cost i).real (Y j) = value a t eta i j) ∧
      (∀ j, 0 ≤ t j - (cost j).real (Y j) ∧ t j - (cost j).real (Y j) ≤ min (t j) eta) ∧
      ∀ i j, |(cost i).real (Y j) - (cost j).real (Y j)| ≤
        (Fintype.card Agent : ℝ)^2 * cellGap a i j := by
  dsimp only
  have ha : ∀ i e, 0 ≤ a i e := fun i e => by rw [hcache]; exact measureReal_nonneg
  obtain ⟨hdis, hdef, _, hgap⟩ := allocation_spec a t eta heta ha hsmall hnormal ht hsum
  have hvalue (i j : Agent) := UpperWholePaymentsPhysical.owned_piece_mass
    cost cells hmeas hcells a hcache (UpperFloating.plan a t) eta i j
  refine ⟨UpperWholePaymentsPhysical.pieces_disjoint cells hcells _ hdis,
    fun j => ⟨UpperWholePaymentsPhysical.piece_measurable cells hmeas _ j,
      UpperWholePaymentsPhysical.piece_subset cells _ j⟩, hvalue, ?_, ?_⟩
  · intro j
    simpa only [hvalue, deficit, allocation, value, UpperWholePayments.value] using hdef j
  · intro i j
    simpa only [hvalue, allocation, value, UpperWholePayments.value] using hgap i j

end EnvyFreeResearch.Full.UpperPayments
