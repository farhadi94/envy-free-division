import EnvyFreeResearch.Full.RefinedUpperLinearSelector
import EnvyFreeResearch.Full.UpperPayments

/-! Concrete Borel whole-cell payments with linear disagreement. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperPayments
open UpperPayments (cellGap cellGap_nonneg difference_le_cellGap cellGap_measurable)
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def allocation (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) : Agent → Finset Cell :=
  RefinedUpperLinearSelector.select a t (cellGap a) eta

def value (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) (i j : Agent) : ℝ :=
  ∑ e ∈ allocation a t eta j, a i e

def deficit (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ) (j : Agent) : ℝ :=
  t j - value a t eta j j

theorem allocation_spec (a : Agent → Cell → ℝ) (t : Agent → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e = 1) (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j ≤ 1) :
    (∀ i j, i ≠ j → Disjoint (allocation a t eta i) (allocation a t eta j)) ∧
      (∀ j, 0 ≤ deficit a t eta j ∧ deficit a t eta j ≤ min (t j) eta) ∧
      (∑ j, deficit a t eta j) ≤ Fintype.card Agent * eta ∧
      ∀ i j, |value a t eta i j - value a t eta j j| ≤
        4 * (Fintype.card Agent : ℝ) * cellGap a i j := by
  cases isEmpty_or_nonempty Agent with
  | inl he =>
    letI := he
    simp
  | inr he =>
    letI := he
    have h := RefinedUpperLinearSelector.select_spec a t (cellGap a) eta heta ha hsmall hnormal ht hsum
      (cellGap_nonneg a) (difference_le_cellGap a) Fintype.card_pos
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    calc
      _ ≤ ∑ _ : Agent, eta := Finset.sum_le_sum (fun j _ => (h.2.1 j).2.trans (min_le_right _ _))
      _ = _ := by simp

section Measurability
variable {X : Type*} [MeasurableSpace X]

theorem allocation_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) : Measurable (fun z => allocation (a z) (t z) (eta z)) :=
  RefinedUpperLinearSelector.select_measurable a t (fun z => cellGap (a z)) eta ha ht
    (cellGap_measurable a ha) heta

theorem value_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) (i j : Agent) : Measurable (fun z => value (a z) (t z) (eta z) i j) := by
  have howned := (measurable_pi_apply j).comp (allocation_measurable a t eta ha ht heta)
  have hv : (fun z => value (a z) (t z) (eta z) i j) =
      fun z => ∑ e, if e ∈ allocation (a z) (t z) (eta z) j then a z i e else 0 := by
    funext z
    simp only [value, Finset.sum_ite_mem_eq]
  rw [hv]
  exact Finset.measurable_sum _ (fun e _ => (ha i e).ite
    ((measurableSet_mem_finset e).preimage howned) measurable_const)

theorem deficit_measurable (a : X → Agent → Cell → ℝ) (t : X → Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (ht : ∀ j, Measurable (fun z => t z j))
    (heta : Measurable eta) (j : Agent) : Measurable (fun z => deficit (a z) (t z) (eta z) j) :=
  (ht j).sub (value_measurable a t eta ha ht heta j j)
end Measurability
end EnvyFreeResearch.Full.RefinedUpperPayments
