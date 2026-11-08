import EnvyFreeResearch.Full.ChoresMulticolorError

/-! Complete whole-cell rounding by dropping sparse equations. Before each
drop a basic feasible point preserves all active equations. Induction on
the finite equation set terminates, while frozen coordinates bound the
error of every dropped equation over the entire remaining construction. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Multicolor
open UpperFloating UpperFloatingStep
open scoped Classical BigOperators

variable {Observer Cell Color : Type*}
  [Fintype Observer] [Fintype Cell] [Fintype Color]

theorem exists_integral_rounding (w : Observer → Cell → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ i e, 0 ≤ w i e ∧ w i e ≤ δ)
    (active : Finset (Observer × Color)) (initial : Cell × Color → ℝ)
    (hbox : Box initial) (hrows : CellSums initial) :
    ∃ y : Cell × Color → ℝ, Box y ∧ CellSums y ∧ Integral y ∧ Frozen initial y ∧
      ∀ row ∈ active, |moment w y row-moment w initial row| ≤ (2*Fintype.card Observer : ℕ)*δ := by
  induction active using Finset.strongInductionOn generalizing initial with
  | _ active ih =>
    obtain ⟨x,hxbox,hxrows,hxmom,hfreeze,hcount⟩ := exists_basic w active initial hbox hrows
    by_cases hempty : fractional x=∅
    · refine ⟨x,hxbox,hxrows,integral_of_fractional_empty x hxbox hempty,hfreeze,?_⟩
      intro row hrow
      rw [hxmom row hrow,sub_self,abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hδ
    · have hpos : 0 < (fractional x).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      obtain ⟨row,hrow,hsparse⟩ := exists_sparse_equation active (fractional x) hpos hcount
      obtain ⟨y,hybox,hyrows,hyint,hyfreeze,hyerror⟩ :=
        ih (active.erase row) (Finset.erase_ssubset hrow) x hxbox hxrows
      refine ⟨y,hybox,hyrows,hyint,frozen_trans initial x y hfreeze hyfreeze,?_⟩
      intro other hother
      rw [← hxmom other hother]
      by_cases heq : other=row
      · subst other
        exact dropped_equation_error w δ hδ hw x y hxbox hybox hyfreeze row hsparse
      · exact hyerror other (Finset.mem_erase.mpr ⟨heq,hother⟩)

theorem integral_row_has_color (y : Cell × Color → ℝ) (hrows : CellSums y)
    (hint : Integral y) (e : Cell) : ∃ j, y (e,j)=1 := by
  by_contra h
  have hz : ∀ j, y (e,j)=0 := fun j => (hint (e,j)).resolve_right (fun hj => h ⟨j,hj⟩)
  have hr := hrows e
  simp only [hz,Finset.sum_const_zero] at hr
  norm_num at hr

theorem integral_color_matrix (y : Cell × Color → ℝ) (hbox : Box y) (hrows : CellSums y)
    (color : Cell → Color) (hcolor : ∀ e, y (e,color e)=1) :
    ∀ e j, y (e,j)=if color e=j then 1 else 0 := by
  intro e j
  by_cases heq : color e=j
  · simpa only [heq,ite_true] using hcolor e
  · rw [if_neg heq]
    have hpair : y (e,color e)+y (e,j) ≤ ∑ q, y (e,q) := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({color e,j} : Finset Color)) (fun q _ _ => (hbox (e,q)).1)
      simpa only [Finset.sum_pair heq] using h
    rw [hcolor,hrows] at hpair
    have hnonneg := (hbox (e,j)).1
    linarith

theorem exists_color_rounding (w : Observer → Cell → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ i e, 0 ≤ w i e ∧ w i e ≤ δ)
    (initial : Cell × Color → ℝ) (hbox : Box initial) (hrows : CellSums initial) :
    ∃ color : Cell → Color, ∀ i j,
      |(∑ e, if color e=j then w i e else 0)-moment w initial (i,j)| ≤
        (2*Fintype.card Observer : ℕ)*δ := by
  obtain ⟨y,hybox,hyrows,hyint,_,hyerror⟩ :=
    exists_integral_rounding w δ hδ hw Finset.univ initial hbox hrows
  choose color hcolor using integral_row_has_color y hyrows hyint
  refine ⟨color,?_⟩
  intro i j
  have hm := hyerror (i,j) (Finset.mem_univ _)
  have heq : moment w y (i,j) = ∑ e, if color e=j then w i e else 0 := by
    unfold moment
    apply Finset.sum_congr rfl
    intro e _
    rw [integral_color_matrix y hybox hyrows color hcolor]
    split_ifs <;> simp
  rwa [heq] at hm

/-- The manuscript's whole-cell multicolor bound, for arbitrary finite
observer/cell/color sets and actual nonnegative normalized weights. -/
theorem whole_cell_rounding (w : Observer → Cell → ℝ) (K : ℝ) (hK : 0 < K)
    (hm : 0 < Fintype.card Color)
    (hw : ∀ i e, 0 ≤ w i e ∧ w i e ≤ 1/K)
    (hnormal : ∀ i, ∑ e, w i e=1) :
    ∃ color : Cell → Color, ∀ i j,
      |(∑ e, if color e=j then w i e else 0)-1/(Fintype.card Color : ℝ)| ≤
        2*(Fintype.card Observer : ℝ)/K := by
  let initial : Cell × Color → ℝ := fun _ => 1/(Fintype.card Color : ℝ)
  have hmreal : (0 : ℝ) < Fintype.card Color := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ Fintype.card Color := by exact_mod_cast hm
  have hbox : Box initial := by
    intro c
    exact ⟨by dsimp [initial]; positivity,by dsimp [initial]; exact (div_le_one hmreal).mpr hmone⟩
  have hrows : CellSums initial := by
    intro e
    simp only [initial,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  obtain ⟨color,hcolor⟩ := exists_color_rounding w (1/K) (by positivity) hw initial hbox hrows
  refine ⟨color,?_⟩
  intro i j
  have hmoment : moment w initial (i,j)=1/(Fintype.card Color : ℝ) := by
    simp only [moment,initial,← Finset.sum_mul,hnormal,one_mul]
  have h := hcolor i j
  rw [hmoment] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv,one_mul] using h

end EnvyFreeResearch.Full.Chores.Multicolor
