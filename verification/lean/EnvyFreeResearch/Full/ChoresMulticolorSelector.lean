import EnvyFreeResearch.Full.ChoresMulticolorRounding

/-! The whole-cell color assignment is obtained by a finite search over
color maps using only the recorded weight table. Its correctness follows
from whole-cell rounding; there are no additional oracle calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Multicolor
open scoped Classical BigOperators

variable {Observer Cell Color : Type*}
  [Fintype Observer] [Fintype Cell] [Fintype Color]

def Good (w : Observer → Cell → ℝ) (K : ℝ) (color : Cell → Color) : Prop :=
  ∀ i j, |(∑ e, if color e=j then w i e else 0)-1/(Fintype.card Color : ℝ)| ≤
    2*(Fintype.card Observer : ℝ)/K

def firstGood (w : Observer → Cell → ℝ) (K : ℝ) (fallback : Color) :
    List (Cell → Color) → (Cell → Color)
  | [] => fun _ => fallback
  | color::rest => if Good w K color then color else firstGood w K fallback rest

theorem firstGood_spec (w : Observer → Cell → ℝ) (K : ℝ) (fallback : Color)
    (candidates : List (Cell → Color)) (hex : ∃ color ∈ candidates, Good w K color) :
    Good w K (firstGood w K fallback candidates) := by
  induction candidates with
  | nil => simp at hex
  | cons color rest ih =>
    by_cases h : Good w K color
    · simpa only [firstGood,ite_eq_left h] using h
    · apply ih (by
        obtain ⟨other,hother,hgood⟩ := hex
        rcases List.mem_cons.mp hother with rfl | hother
        · exact (h hgood).elim
        · exact ⟨other,hother,hgood⟩) |> fun hh => ?_
      simpa only [firstGood,ite_eq_right h] using hh

def select (w : Observer → Cell → ℝ) (K : ℝ) (fallback : Color) : Cell → Color :=
  firstGood w K fallback Finset.univ.toList

theorem select_good (w : Observer → Cell → ℝ) (K : ℝ) (hK : 0 < K) (fallback : Color)
    (hw : ∀ i e, 0 ≤ w i e ∧ w i e ≤ 1/K) (hnormal : ∀ i, ∑ e, w i e=1) :
    Good w K (select w K fallback) := by
  apply firstGood_spec
  obtain ⟨color,hcolor⟩ := whole_cell_rounding w K hK
    (Fintype.card_pos_iff.mpr ⟨fallback⟩) hw hnormal
  exact ⟨color,by simp,hcolor⟩

end EnvyFreeResearch.Full.Chores.Multicolor
