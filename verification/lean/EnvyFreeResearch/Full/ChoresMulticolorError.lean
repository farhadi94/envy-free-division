import EnvyFreeResearch.Full.ChoresMulticolorCounting
import EnvyFreeResearch.NearExact

/-! Once a sparse observer/color equation is dropped, frozen integral
coordinates and permanently zero variables restrict its entire future
error to the fractional coordinates present at the time of dropping. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Multicolor
open UpperFloating UpperFloatingStep
open scoped Classical BigOperators

variable {Observer Cell Color : Type*}
  [Fintype Observer] [Fintype Cell] [Fintype Color]

def Box (x : Cell × Color → ℝ) : Prop := ∀ c, 0 ≤ x c ∧ x c ≤ 1
def CellSums (x : Cell × Color → ℝ) : Prop := ∀ e, ∑ j, x (e,j)=1
def Integral (x : Cell × Color → ℝ) : Prop := ∀ c, x c=0 ∨ x c=1

theorem integral_coordinate (x : Cell × Color → ℝ) (hbox : Box x)
    (c : Cell × Color) (hnot : c ∉ fractional x) : x c=0 ∨ x c=1 := by
  have h := hbox c
  have hn : ¬(0 < x c ∧ x c < 1) := by simpa only [fractional,Finset.mem_filter,
    Finset.mem_univ,true_and] using hnot
  by_cases hzero : x c=0
  · exact Or.inl hzero
  · exact Or.inr (le_antisymm h.2 (le_of_not_gt (fun hc =>
      hn ⟨lt_of_le_of_ne h.1 (Ne.symm hzero),hc⟩)))

theorem integral_of_fractional_empty (x : Cell × Color → ℝ) (hbox : Box x)
    (hempty : fractional x=∅) : Integral x :=
  fun c => integral_coordinate x hbox c (by simp [hempty])

theorem frozen_trans (x y z : Cell × Color → ℝ) (hxy : Frozen x y) (hyz : Frozen y z) : Frozen x z := by
  intro c hc
  have heq := hxy c hc
  have hy : y c=0 ∨ y c=1 := by simpa only [heq] using hc
  exact (hyz c hy).trans heq

def weighted (w : Observer → Cell → ℝ) (row : Observer × Color) (c : Cell × Color) : ℝ :=
  if c.2=row.2 then w row.1 c.1 else 0

theorem weighted_moment (w : Observer → Cell → ℝ) (row : Observer × Color)
    (x : Cell × Color → ℝ) : (∑ c, weighted w row c*x c)=moment w x row := by
  simp [weighted,moment,Fintype.sum_prod_type]

theorem dropped_equation_error (w : Observer → Cell → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ i e, 0 ≤ w i e ∧ w i e ≤ δ)
    (x y : Cell × Color → ℝ) (hx : Box x) (hy : Box y) (hfrozen : Frozen x y)
    (row : Observer × Color) (hcount : (rowSupport (fractional x) row).card ≤ 2*Fintype.card Observer) :
    |moment w y row-moment w x row| ≤ (2*Fintype.card Observer : ℕ)*δ := by
  have h := NearExact.finite_error_bound_of_card_le
    (rowSupport (fractional x) row) (fun c => weighted w row c*y c)
    (fun c => weighted w row c*x c) δ (2*Fintype.card Observer) hδ hcount
  rw [weighted_moment,weighted_moment] at h
  apply h
  · intro c hc
    have heq := (Finset.mem_filter.mp hc).2
    simp only [weighted,heq,ite_true]
    have hwy0 : 0 ≤ w row.1 c.1*y c := mul_nonneg (hw _ _).1 (hy c).1
    have hwy1 : w row.1 c.1*y c ≤ w row.1 c.1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hy c).2 (hw _ _).1
    simpa only [mul_comm] using NearExact.one_cell_rounding_error (w row.1 c.1)
      (w row.1 c.1*y c) (x c) δ (hw _ _).1 (hw _ _).2 hwy0 hwy1 (hx c).1 (hx c).2
  · intro c hc
    by_cases heq : c.2=row.2
    · have hnot : c ∉ fractional x := fun h => hc (Finset.mem_filter.mpr ⟨h,heq⟩)
      rw [hfrozen c (integral_coordinate x hx c hnot)]
    · simp only [weighted,heq,ite_false,zero_mul]

end EnvyFreeResearch.Full.Chores.Multicolor
