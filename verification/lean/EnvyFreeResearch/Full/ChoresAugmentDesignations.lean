import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Geometrically growing designated sets admit distinct choices that no
earlier augmenter touched. This selects actual minimum-cost bundles once
the reverse augmentation loop has established its threshold invariant. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open scoped Classical BigOperators

variable {Piece : Type*} [LinearOrder Piece]

theorem sum_powers_two (k : ℕ) : (∑ j ∈ Finset.range k, (2 : ℕ)^j)+1=2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,pow_succ]
    omega

def earlier (D : ℕ → Finset Piece) (i : ℕ) : Finset Piece := (Finset.range i).biUnion D
def freshSet (D : ℕ → Finset Piece) (i : ℕ) : Finset Piece := D i \ earlier D i

theorem earlier_card_lt (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) (i : Fin k) : (earlier D i.val).card < (D i.val).card := by
  have hle : (earlier D i.val).card ≤ ∑ j ∈ Finset.range i.val, (D j).card := Finset.card_biUnion_le
  have heq : (∑ j ∈ Finset.range i.val, (D j).card) = ∑ j ∈ Finset.range i.val, (2 : ℕ)^j :=
    Finset.sum_congr rfl (fun j hj => hcount j ((Finset.mem_range.mp hj).trans i.isLt))
  rw [heq] at hle
  rw [hcount i.val i.isLt]
  have hsum := sum_powers_two i.val
  omega

theorem fresh_nonempty (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) (i : Fin k) : (freshSet D i.val).Nonempty := by
  obtain ⟨p,hp,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card (earlier_card_lt D k hcount i)
  exact ⟨p,Finset.mem_sdiff.mpr ⟨hp,hnot⟩⟩

def chooseFresh (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) (i : Fin k) : Piece :=
  (freshSet D i.val).min' (fresh_nonempty D k hcount i)

theorem chooseFresh_mem (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) (i : Fin k) :
    chooseFresh D k hcount i ∈ D i.val ∧ chooseFresh D k hcount i ∉ earlier D i.val :=
  Finset.mem_sdiff.mp (Finset.min'_mem _ _)

theorem chooseFresh_injective (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i) : Function.Injective (chooseFresh D k hcount) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hnot := (chooseFresh_mem D k hcount j).2
    apply hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨i.val,Finset.mem_range.mpr hij,heq ▸ (chooseFresh_mem D k hcount i).1⟩
  · have hnot := (chooseFresh_mem D k hcount i).2
    apply hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨j.val,Finset.mem_range.mpr hji,heq.symm ▸ (chooseFresh_mem D k hcount j).1⟩

theorem designated_choices_envy_free (D : ℕ → Finset Piece) (k : ℕ)
    (hcount : ∀ i < k, (D i).card=2^i)
    (available : Finset Piece) (hpublic : ∀ i < k, D i ⊆ available)
    (value : Fin k → Piece → ℝ) (threshold : Fin k → ℝ)
    (hfloor : ∀ i p, p ∈ available → threshold i ≤ value i p)
    (huntouched : ∀ i p, p ∈ D i.val → p ∉ earlier D i.val → value i p=threshold i) :
    Function.Injective (chooseFresh D k hcount) ∧
      (∀ i, chooseFresh D k hcount i ∈ available) ∧
      ∀ i j, value i (chooseFresh D k hcount i) ≤ value i (chooseFresh D k hcount j) := by
  have hchosen (i : Fin k) : chooseFresh D k hcount i ∈ available :=
    hpublic i.val i.isLt (chooseFresh_mem D k hcount i).1
  refine ⟨chooseFresh_injective D k hcount,hchosen,?_⟩
  intro i j
  rw [huntouched i _ (chooseFresh_mem D k hcount i).1 (chooseFresh_mem D k hcount i).2]
  exact hfloor i _ (hchosen j)

end EnvyFreeResearch.Full.Chores.Augment
