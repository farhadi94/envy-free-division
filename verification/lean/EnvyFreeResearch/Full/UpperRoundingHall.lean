import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hall matching from fractional slot capacities and trimming

These lemmas use the actual fractional edge masses to prove Hall's condition.
Trimming repeatedly deletes cells until the first crossing of the target.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRounding

variable {Slot Cell : Type*} [Fintype Slot] [Fintype Cell]

/-- Fractional unit demands and unit cell capacities imply an actual injective
matching, supported on strictly positive fractional edges. -/
theorem matching_of_fractional (b : Slot → Cell → ℝ)
    (hzero : ∀ s e, 0 ≤ b s e) (hslot : ∀ s, ∑ e, b s e = 1)
    (hcell : ∀ e, ∑ s, b s e ≤ 1) :
    ∃ m : Slot → Cell, Function.Injective m ∧ ∀ s, 0 < b s (m s) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun s e => 0 < b s e)).mp
  intro A
  let B : Finset Cell := Finset.univ.filter (fun e => ∃ s ∈ A, 0 < b s e)
  have hsupport (e : Cell) (he : e ∉ B) (s : Slot) (hs : s ∈ A) : b s e = 0 := by
    apply le_antisymm _ (hzero s e)
    by_contra h
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, hs, lt_of_not_ge h⟩)
  have hcap (e : Cell) : ∑ s ∈ A, b s e ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun s _ _ => hzero s e)).trans (hcell e)
  have hreal : (A.card : ℝ) ≤ B.card := calc
    (A.card : ℝ) = ∑ s ∈ A, ∑ e, b s e := by simp [hslot]
    _ = ∑ e, ∑ s ∈ A, b s e := Finset.sum_comm
    _ = ∑ e ∈ B, ∑ s ∈ A, b s e := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro e _ he
      exact Finset.sum_eq_zero (fun s hs => hsupport e he s hs)
    _ ≤ ∑ _e ∈ B, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcap e)
    _ = (B.card : ℝ) := by simp
  exact_mod_cast hreal

omit [Fintype Cell] in
/-- Starting above the target, finite repeated deletion reaches its first
crossing. The last deleted cell has value at most `eta`. No assumption about
one predetermined cell sufficing is made. -/
theorem trim_above (a : Cell → ℝ) (eta target : ℝ)
    (hbound : ∀ e, a e ≤ eta) (htarget : 0 ≤ target) (S : Finset Cell)
    (hlarge : target < ∑ e ∈ S, a e) :
    ∃ T ⊆ S, target - eta ≤ ∑ e ∈ T, a e ∧ ∑ e ∈ T, a e ≤ target := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hlarge; linarith
  | @insert e S he ih =>
    by_cases hremain : target < ∑ z ∈ S, a z
    · obtain ⟨T, hT, hlo, hhi⟩ := ih hremain
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨S, Finset.subset_insert _ _, ?_, le_of_not_gt hremain⟩
      rw [Finset.sum_insert he] at hlarge
      linarith [hbound e]

omit [Fintype Cell] in
/-- Trimming preserves a lower bound already known for a matched load. -/
theorem trim_load (a : Cell → ℝ) (eta target : ℝ)
    (hbound : ∀ e, a e ≤ eta) (htarget : 0 ≤ target) (S : Finset Cell)
    (hlower : target - eta ≤ ∑ e ∈ S, a e) :
    ∃ T ⊆ S, target - eta ≤ ∑ e ∈ T, a e ∧ ∑ e ∈ T, a e ≤ target := by
  by_cases hlarge : target < ∑ e ∈ S, a e
  · exact trim_above a eta target hbound htarget S hlarge
  · exact ⟨S, Finset.Subset.refl _, hlower, le_of_not_gt hlarge⟩

end EnvyFreeResearch.Full.UpperRounding
