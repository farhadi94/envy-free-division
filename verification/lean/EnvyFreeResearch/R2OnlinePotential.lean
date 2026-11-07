import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-!
# Finite progress certificates for immediate-repair completion

Rows list proper dominated targets. Physical bundle transport and repair must
establish the inclusion and fresh-witness hypotheses below; this module does
not assert those analytic interfaces or probabilistic success estimates.
-/

namespace EnvyFreeResearch.R2OnlinePotential

open scoped BigOperators

variable {Agent : Type*}

abbrev TargetRows (Agent : Type*) := Agent → Finset Agent

def Proper (rows : TargetRows Agent) : Prop := ∀ i, i ∉ rows i

def potential [Fintype Agent] (rows : TargetRows Agent) : ℕ :=
  ∑ i, (rows i).card

theorem transported_row_card_le [DecidableEq Agent]
    (old new : TargetRows Agent) (f : Equiv.Perm Agent)
    (htransport : ∀ i, (old i).image f ⊆ new i) (i : Agent) :
    (old i).card ≤ (new i).card := by
  calc
    (old i).card = ((old i).image f).card :=
      (Finset.card_image_of_injective _ f.injective).symm
    _ ≤ (new i).card := Finset.card_le_card (htransport i)

/-- The new target is genuinely outside the image of the old target set. -/
theorem fresh_target_not_in_image [DecidableEq Agent]
    (old : TargetRows Agent) (f : Equiv.Perm Agent) (b h : Agent)
    (hfresh : h ∉ old b) : f h ∉ (old b).image f := by
  intro hin
  rcases Finset.mem_image.mp hin with ⟨j, hj, hjeq⟩
  exact hfresh ((f.injective hjeq) ▸ hj)

theorem fresh_target_strict_row [DecidableEq Agent]
    (old new : TargetRows Agent) (f : Equiv.Perm Agent)
    (htransport : ∀ i, (old i).image f ⊆ new i)
    (b h : Agent) (hfresh : h ∉ old b) (hnew : f h ∈ new b) :
    (old b).card < (new b).card := by
  have hstrict : (old b).image f ⊂ new b := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨htransport b, ?_⟩
    intro heq
    have hmem : f h ∈ (old b).image f := by simpa [heq] using hnew
    exact fresh_target_not_in_image old f b h hfresh hmem
  have hcard := Finset.card_lt_card hstrict
  simpa only [Finset.card_image_of_injective _ f.injective] using hcard

/-- A common injective label transport and one new target force strict global progress. -/
theorem potential_increases [Fintype Agent] [DecidableEq Agent]
    (old new : TargetRows Agent) (f : Equiv.Perm Agent)
    (htransport : ∀ i, (old i).image f ⊆ new i)
    (b h : Agent) (hfresh : h ∉ old b) (hnew : f h ∈ new b) :
    potential old + 1 ≤ potential new := by
  apply Nat.succ_le_of_lt
  apply Finset.sum_lt_sum
  · intro i _
    exact transported_row_card_le old new f htransport i
  · exact ⟨b, Finset.mem_univ b, fresh_target_strict_row old new f htransport b h hfresh hnew⟩

theorem row_card_le [Fintype Agent] [DecidableEq Agent]
    (rows : TargetRows Agent) (hproper : Proper rows) (i : Agent) :
    (rows i).card ≤ Fintype.card Agent - 1 := by
  have hsub : rows i ⊆ Finset.univ.erase i := by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ j⟩
    intro heq
    exact hproper i (heq ▸ hj)
  simpa using Finset.card_le_card hsub

theorem potential_le [Fintype Agent] [DecidableEq Agent]
    (rows : TargetRows Agent) (hproper : Proper rows) :
    potential rows ≤ Fintype.card Agent * (Fintype.card Agent - 1) := by
  calc
    potential rows ≤ ∑ _i : Agent, (Fintype.card Agent - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact row_card_le rows hproper i
    _ = Fintype.card Agent * (Fintype.card Agent - 1) := by simp

/-- A single missing proper comparison certifies that the potential is not saturated. -/
theorem potential_lt_of_missing [Fintype Agent] [DecidableEq Agent]
    (rows : TargetRows Agent) (hproper : Proper rows)
    (a b : Agent) (hne : b ≠ a) (hmissing : b ∉ rows a) :
    potential rows < Fintype.card Agent * (Fintype.card Agent - 1) := by
  have hsub : rows a ⊆ Finset.univ.erase a := by
    intro j hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
    intro heq
    exact hproper a (heq ▸ hj)
  have hstrict : rows a ⊂ Finset.univ.erase a := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    apply hmissing
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩
  have hrow : (rows a).card < Fintype.card Agent - 1 := by
    simpa using Finset.card_lt_card hstrict
  have hs : (∑ i, (rows i).card) < ∑ _i : Agent, (Fintype.card Agent - 1) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact row_card_le rows hproper i
    · exact ⟨a, Finset.mem_univ a, hrow⟩
  simpa [potential] using hs

/-- Strict integer progress accumulates over a finite run. -/
theorem accumulated_progress (p : ℕ → ℕ) (rounds : ℕ)
    (hstep : ∀ t < rounds, p t + 1 ≤ p (t + 1)) :
    p 0 + rounds ≤ p rounds := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      have hind := ih (fun t ht => hstep t (by omega))
      have hlast := hstep rounds (by omega)
      omega

theorem nonterminal_rounds_le [Fintype Agent] [DecidableEq Agent]
    (states : ℕ → TargetRows Agent) (rounds : ℕ)
    (hfinal : Proper (states rounds))
    (hstep : ∀ t < rounds, potential (states t) + 1 ≤ potential (states (t + 1))) :
    rounds ≤ Fintype.card Agent * (Fintype.card Agent - 1) := by
  have hgrowth := accumulated_progress (fun t => potential (states t)) rounds hstep
  have hbound := potential_le (states rounds) hfinal
  omega

/-- Includes a possible final iteration that terminates without a new potential value.
Its start guard is necessary to avoid an erroneous extra +1 in the round bound. -/
theorem all_rounds_le_from_start_guard (p : ℕ → ℕ) (rounds cap : ℕ)
    (hstep : ∀ t, t + 1 < rounds → p t + 1 ≤ p (t + 1))
    (hguard : ∀ t < rounds, p t < cap) : rounds ≤ cap := by
  cases rounds with
  | zero => omega
  | succ rounds =>
      have hgrowth := accumulated_progress p rounds (fun t ht => hstep t (by omega))
      have hlast := hguard rounds (by omega)
      omega

/-- Complete finite iteration certificate using only proper target rows and a missing edge
at each iteration's start. The last iteration is allowed to finish early. -/
theorem all_rounds_le [Fintype Agent] [DecidableEq Agent]
    (states : ℕ → TargetRows Agent) (rounds : ℕ)
    (hproper : ∀ t < rounds, Proper (states t))
    (hstep : ∀ t, t + 1 < rounds →
      potential (states t) + 1 ≤ potential (states (t + 1)))
    (hmissing : ∀ t < rounds, ∃ a b, b ≠ a ∧ b ∉ states t a) :
    rounds ≤ Fintype.card Agent * (Fintype.card Agent - 1) := by
  apply all_rounds_le_from_start_guard (fun t => potential (states t)) rounds _ hstep
  intro t ht
  obtain ⟨a, b, hne, hmiss⟩ := hmissing t ht
  exact potential_lt_of_missing (states t) (hproper t ht) a b hne hmiss

#print axioms fresh_target_not_in_image
#print axioms potential_increases
#print axioms potential_lt_of_missing
#print axioms accumulated_progress
#print axioms nonterminal_rounds_le
#print axioms all_rounds_le

end EnvyFreeResearch.R2OnlinePotential
