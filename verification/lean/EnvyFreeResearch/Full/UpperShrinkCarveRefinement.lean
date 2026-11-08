import EnvyFreeResearch.Full.UpperShrinkCarveRounding

/-! Exact lifting of fractional colors to queried children, followed by
the fixed finite floating selector. Old integral colors cannot become
fractional, so each surviving split cell inherits the depth bound. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve

variable {Agent Cell Child : Type*} [Fintype Agent] [Fintype Cell] [Fintype Child]

def inherit (parent : Child → Cell) (x : Cell → Option Agent → ℝ) :
    UpperFloating.PaymentCoord Agent Child → ℝ := fun c => x (parent c.1) c.2

theorem inherited_moment (parent : Child → Cell)
    (a : Agent → Cell → ℝ) (b : Agent → Child → ℝ) (x : Cell → Option Agent → ℝ)
    (hpartition : ∀ i e, (∑ d, if parent d = e then b i d else 0) = a i e)
    (i j : Agent) :
    (∑ d, b i d * inherit parent x (d,some j)) = ∑ e, a i e * x e (some j) := by
  calc
    _ = ∑ d, ∑ e, if parent d = e then b i d * x e (some j) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      simp [inherit]
    _ = ∑ e, (∑ d, if parent d = e then b i d else 0) * x e (some j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = _ := by simp_rw [hpartition]

def refloat (parent : Child → Cell) (b : Agent → Child → ℝ)
    (x : Cell → Option Agent → ℝ) (d : Child) (c : Option Agent) : ℝ :=
  UpperFloating.select b (inherit parent x) (d,c)

theorem refloat_spec (parent : Child → Cell)
    (a : Agent → Cell → ℝ) (b : Agent → Child → ℝ) (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hrow : ∀ e, ∑ c, x e c = 1)
    (hpartition : ∀ i e, (∑ d, if parent d = e then b i d else 0) = a i e) :
    (∀ d c, 0 ≤ refloat parent b x d c ∧ refloat parent b x d c ≤ 1) ∧
    (∀ d, ∑ c, refloat parent b x d c = 1) ∧
    (∀ i j, (∑ d, b i d * refloat parent b x d (some j)) = ∑ e, a i e * x e (some j)) ∧
    (UpperWholePayments.splitCells (refloat parent b x)).card ≤ Fintype.card Agent ^ 2 := by
  obtain ⟨hb,hr,hm,_,hc⟩ := UpperFloating.select_spec b (inherit parent x)
    (fun c => hbox (parent c.1) c.2) (fun d => hrow (parent d))
  refine ⟨fun d c => hb (d,c),hr,?_,?_⟩
  · intro i j
    exact (hm i j).trans (inherited_moment parent a b x hpartition i j)
  · have heq : UpperWholePayments.splitCells (refloat parent b x) =
        UpperFloating.splitCells (UpperFloating.select b (inherit parent x)) := by
      rw [UpperFloating.splitCells_eq_filter]
      ext d
      constructor
      · intro hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hd).2⟩
      · intro hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hd).2⟩
    rw [heq]
    exact hc

theorem refloat_split_parent (parent : Child → Cell) (b : Agent → Child → ℝ)
    (x : Cell → Option Agent → ℝ) (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hrow : ∀ e, ∑ c, x e c = 1) (d : Child)
    (hd : d ∈ UpperWholePayments.splitCells (refloat parent b x)) :
    parent d ∈ UpperWholePayments.splitCells x := by
  have hs := floated_split_subset b (inherit parent x)
    (fun c => hbox (parent c.1) c.2) (fun d => hrow (parent d)) hd
  obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,hc⟩

theorem refloat_halving (parent : Child → Cell)
    (a : Agent → Cell → ℝ) (b : Agent → Child → ℝ) (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hrow : ∀ e, ∑ c, x e c = 1)
    (eta : ℝ)
    (hsmall : ∀ i e, e ∈ UpperWholePayments.splitCells x → a i e ≤ eta)
    (hhalf : ∀ i d, parent d ∈ UpperWholePayments.splitCells x → b i d ≤ a i (parent d) / 2)
    (i : Agent) (d : Child) (hd : d ∈ UpperWholePayments.splitCells (refloat parent b x)) :
    b i d ≤ eta / 2 := by
  have hp := refloat_split_parent parent b x hbox hrow d hd
  exact (hhalf i d hp).trans (div_le_div_of_nonneg_right (hsmall i (parent d) hp) (by norm_num))

end EnvyFreeResearch.Full.UpperShrinkCarve
