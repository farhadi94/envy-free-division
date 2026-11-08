import EnvyFreeResearch.Full.ChoresAtomProtection
import Mathlib.Data.Finset.Max

/-! Finite suffix costs on the immutable original atom chain. These are
cached finite sums; later geometry lemmas identify them with the actual
original equalizer gaps and physical offered suffixes. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical BigOperators

variable {n : ℕ}

def tailCost (w : Fin n → Fin n → ℝ) (i : Fin n) (t : ℕ) : ℝ :=
  ∑ a, if t ≤ a.val then w i a else 0

theorem tail_nonnegative (w : Fin n → Fin n → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (i : Fin n) (t : ℕ) : 0 ≤ tailCost w i t := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> simp_all

theorem tail_end (w : Fin n → Fin n → ℝ) (i : Fin n) : tailCost w i n=0 := by
  apply Finset.sum_eq_zero
  intro a ha
  simp only [not_le_of_gt a.isLt,ite_false]

theorem tail_antitone (w : Fin n → Fin n → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (i : Fin n) {s t : ℕ} (hst : s ≤ t) : tailCost w i t ≤ tailCost w i s := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases ht : t ≤ a.val
  · simp only [ht,hst.trans ht,ite_true,le_refl]
  · simp only [ht,ite_false]
    split_ifs <;> simp_all

theorem atom_le_tail (w : Fin n → Fin n → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (i a : Fin n) (t : ℕ) (ht : t ≤ a.val) : w i a ≤ tailCost w i t := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b : Fin n => if t ≤ b.val then w i b else 0)
    (fun b hb => by split_ifs <;> simp_all) (Finset.mem_univ a)
  simpa only [tailCost,ht,ite_true] using h

theorem tail_step (w : Fin n → Fin n → ℝ) (i a : Fin n) :
    tailCost w i a.val=w i a+tailCost w i (a.val+1) := by
  have hpoint (b : Fin n) : (if a.val ≤ b.val then w i b else 0)=
      (if b=a then w i a else 0)+(if a.val+1 ≤ b.val then w i b else 0) := by
    by_cases h : b=a
    · subst b; simp
    · have hne : b.val ≠ a.val := fun heq => h (Fin.ext heq)
      by_cases hlt : a.val < b.val
      · simp [h,hlt.le,show a.val+1 ≤ b.val by omega]
      · simp [h,show ¬ a.val ≤ b.val by omega,show ¬ a.val+1 ≤ b.val by omega]
  unfold tailCost
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem tail_small (w : Fin n → Fin n → ℝ) (i : Fin n) (t : ℕ) (r H : ℝ)
    (hr : 0 ≤ r) (hH : 0 < H) (hsmall : ∀ a, t ≤ a.val → w i a ≤ r/H) :
    tailCost w i t ≤ (n : ℝ)*r/H := by
  calc
    tailCost w i t ≤ ∑ _a : Fin n, r/H := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · exact hsmall a h
      · exact div_nonneg hr hH.le
    _ = _ := by simp; ring

theorem separated_gap_contradiction (r H : ℝ) (hr : 0 < r) (hH : 0 < H)
    (hscale : (n : ℝ) < H*H) (v : ℝ) (hlarge : H*r ≤ v) (hsmall : v ≤ (n : ℝ)*r/H) : False :=
  R5ChoreMatching.omitted_mark_contradiction n r H v hr hH hscale hlarge hsmall

theorem small_not_large (r H v : ℝ) (hr : 0 < r) (hH : 1 < H)
    (hsmall : v ≤ r/H) : ¬ H*r ≤ v := by
  intro hlarge
  have hHpos : 0 < H := by linarith
  have hmul := (le_div_iff₀ hHpos).mp (hlarge.trans hsmall)
  nlinarith [mul_pos hr (show 0 < H*H-1 by nlinarith)]

end EnvyFreeResearch.Full.Chores.Frontier
