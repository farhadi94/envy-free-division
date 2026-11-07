import Mathlib

/-!
# Round 3: finite chore ancestry and discrepancy certificates

These statements certify the finite cost algebra used by the deterministic
construction. They do not construct interval prefixes, prove the physical
ancestry invariant, implement Core/SubCore, or formalize an oracle protocol.
The input inequalities must be supplied by those separate written proofs.
-/

namespace EnvyFreeResearch.R3ChoreAncestry

open scoped BigOperators

theorem signed_gap_identity (value baseline : ℝ) :
    value - baseline = max 0 (value - baseline) - max 0 (baseline - value) := by
  by_cases h : baseline ≤ value
  · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
    ring
  · have h' : value ≤ baseline := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left (sub_nonpos.mpr h'), max_eq_right (sub_nonneg.mpr h')]
    ring

/-- Paying every negative baseline deficit leaves every positive one intact. -/
theorem surplus_bound {Snapshot : Type*} (S : Finset Snapshot)
    (value baseline : Snapshot → ℝ) (credit : ℝ)
    (hcredit : (∑ s ∈ S, max 0 (baseline s - value s)) ≤ credit) :
    (∑ s ∈ S, max 0 (value s - baseline s)) ≤
      credit + ∑ s ∈ S, (value s - baseline s) := by
  have hid : (∑ s ∈ S, (value s - baseline s)) =
      (∑ s ∈ S, max 0 (value s - baseline s)) -
      (∑ s ∈ S, max 0 (baseline s - value s)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    exact signed_gap_identity (value s) (baseline s)
  linarith

/-- A single physical witness survives the accounting for every other piece. -/
theorem witness_surplus {Snapshot : Type*} (S : Finset Snapshot)
    (value baseline : Snapshot → ℝ) (credit threshold : ℝ)
    (hcredit : (∑ s ∈ S, max 0 (baseline s - value s)) ≤ credit)
    (w : Snapshot) (hw : w ∈ S) (hmarked : threshold ≤ value w - baseline w) :
    threshold ≤ credit + ∑ s ∈ S, (value s - baseline s) := by
  have hnonnegative : ∀ s ∈ S, 0 ≤ max 0 (value s - baseline s) := by
    intro s hs
    exact le_max_left _ _
  have hsingle := Finset.single_le_sum hnonnegative hw
  have hpos : value w - baseline w ≤ max 0 (value w - baseline w) := le_max_right _ _
  have hsurplus := surplus_bound S value baseline credit hcredit
  linarith

/-- Donor resets consume donor reserves; the survivor keeps its own reserve. -/
theorem reserve_transition (credit deficit donorReserve survivorReserve ownRemoval
    newDeficit newReserve recipientLoss survivorGrowth : ℝ)
    (hold : deficit + donorReserve + survivorReserve ≤ credit)
    (hdeficit : newDeficit ≤ deficit + donorReserve + recipientLoss)
    (hreserve : newReserve ≤ survivorReserve + survivorGrowth)
    (hpayment : recipientLoss + survivorGrowth ≤ ownRemoval) :
    newDeficit + newReserve ≤ credit + ownRemoval := by
  linarith

/-- Past recipients and future recipients spend the payment in disjoint cases. -/
theorem exclusive_payment (ownRemoval recipientLoss survivorGrowth : ℝ)
    (hcases : (recipientLoss ≤ ownRemoval ∧ survivorGrowth = 0) ∨
      (recipientLoss = 0 ∧ survivorGrowth ≤ ownRemoval)) :
    recipientLoss + survivorGrowth ≤ ownRemoval := by
  rcases hcases with ⟨hloss, hgrowth⟩ | ⟨hloss, hgrowth⟩ <;> linarith

/-- The unchanged-pointer large-atom exit has no new survivor charge. -/
theorem first_large_payment (ownRemoval recipientLoss : ℝ)
    (hcake : recipientLoss ≤ ownRemoval) :
    recipientLoss + (0 : ℝ) ≤ ownRemoval := by simpa using hcake

/-- A lower bound on an intact near-exact piece protects the whole other group. -/
theorem discrepancy_cross (own other source target scale : ℝ)
    (hscale : 0 < scale)
    (hown : own ≤ target)
    (hratio : scale * target ≤ source)
    (hpiece : source / scale ≤ other) : own ≤ other := by
  have htarget : target ≤ source / scale := (le_div_iff₀ hscale).mpr (by
    simpa [mul_comm] using hratio)
  exact hown.trans (htarget.trans hpiece)

/-- Parent EF margins add to the independently EF complete discrepancy addition. -/
theorem add_ef (oldOwn oldOther newOwn newOther : ℝ)
    (hold : oldOwn ≤ oldOther) (hnew : newOwn ≤ newOther) :
    oldOwn + newOwn ≤ oldOther + newOther := add_le_add hold hnew

end EnvyFreeResearch.R3ChoreAncestry
