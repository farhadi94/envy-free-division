import EnvyFreeResearch.Full.UpperFloatingStep

/-! Counting split cells, including the unused color. -/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperFloating

open UpperFloatingStep

variable {Cell Color : Type*} [Fintype Cell] [Fintype Color]

def splitCells (x : Cell × Color → ℝ) : Finset Cell := (fractional x).image Prod.fst


theorem splitCells_eq_filter (x : Cell × Color → ℝ) :
    splitCells x = Finset.univ.filter (fun e => ∃ j, 0 < x (e, j) ∧ x (e, j) < 1) := by
  ext e
  simp [splitCells, fractional]

/-- A cell with one strictly fractional color has a second strictly
fractional color, because every color is nonnegative and its row sums to one.
The unused color is part of this row. -/
theorem split_has_two_fractional (x : Cell × Color → ℝ)
    (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hrow : ∀ e, ∑ j, x (e, j) = 1)
    (e : Cell) (he : e ∈ splitCells x) :
    ∃ p q : Color, p ≠ q ∧ (e, p) ∈ fractional x ∧ (e, q) ∈ fractional x := by
  classical
  obtain ⟨⟨f, p⟩, hp, hfp⟩ := Finset.mem_image.mp he
  dsimp at hfp
  subst f
  have hpf : 0 < x (e, p) ∧ x (e, p) < 1 := (Finset.mem_filter.mp hp).2
  have hsum := Finset.sum_erase_add (Finset.univ : Finset Color)
    (fun q => x (e, q)) (Finset.mem_univ p)
  rw [hrow] at hsum
  have hpos : 0 < ∑ q ∈ (Finset.univ : Finset Color).erase p, x (e, q) := by linarith
  obtain ⟨q, hq, hqpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun q _ => (hbox (e, q)).1)).mp hpos
  have hpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
  have hpair : x (e, p) + x (e, q) ≤ 1 := calc
    _ = ∑ r ∈ ({p, q} : Finset Color), x (e, r) := by simp [hpq]
    _ ≤ ∑ r, x (e, r) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun r _ _ => (hbox (e, r)).1)
    _ = 1 := hrow e
  refine ⟨p, q, hpq, hp, ?_⟩
  have hqone : x (e, q) < 1 := by linarith
  simp [fractional, hqpos, hqone]

/-- Each split cell contributes at least two distinct fractional coordinates.
This counts sharing with the unused color on the same footing as recipients. -/
theorem twice_split_le_fractional (x : Cell × Color → ℝ)
    (hbox : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hrow : ∀ e, ∑ j, x (e, j) = 1) :
    2 * (splitCells x).card ≤ (fractional x).card := by
  classical
  have hex (e : splitCells x) := split_has_two_fractional x hbox hrow e e.property
  choose p q hne hp hq using hex
  let injection : splitCells x × Bool → fractional x := fun eb =>
    ⟨(eb.1, if eb.2 then p eb.1 else q eb.1), by
      cases h : eb.2 <;> simp [hp, hq]⟩
  have hinj : Function.Injective injection := by
    rintro ⟨e, b⟩ ⟨f, c⟩ h
    have hef : e = f := Subtype.ext (congrArg (fun z : fractional x => z.val.1) h)
    subst f
    suffices hbc : b = c by cases hbc; rfl
    cases b <;> cases c
    · rfl
    · have heq : q e = p e := congrArg (fun z : fractional x => z.val.2) h
      exact False.elim (hne e heq.symm)
    · have heq : p e = q e := congrArg (fun z : fractional x => z.val.2) h
      exact False.elim (hne e heq)
    · rfl
  have hc := Fintype.card_le_of_injective injection hinj
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] at hc
  omega

end EnvyFreeResearch.Full.UpperFloating
