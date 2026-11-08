import EnvyFreeResearch.Full.UpperFloating
import EnvyFreeResearch.Full.UpperWholePayments

/-! Final one-sided rounding for logarithmic-precision carving. Only cells
that are still fractional are discarded to the dummy; integral colors are
retained. The error depends on the remaining fractional mass, not on the
number or sizes of already integral physical components. -/

noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem integral_moment_bounds (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (f delta : ℝ)
    (ha : ∀ i e, 0 ≤ a i e)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hrow : ∀ e, ∑ c, x e c = 1)
    (hmoment : ∀ i j, ∑ e, a i e * x e (some j) = f)
    (hloss : ∀ i, ∑ e ∈ UpperWholePayments.splitCells x, a i e ≤ delta)
    (i j : Agent) :
    f - delta ≤ ∑ e ∈ UpperWholePayments.integralCells x j, a i e ∧
      (∑ e ∈ UpperWholePayments.integralCells x j, a i e) ≤ f := by
  have hd := UpperWholePayments.fractional_decomposition a x hbox hrow i j
  change (∑ e, a i e * x e (some j)) = _ at hd
  rw [hmoment] at hd
  have hn : 0 ≤ ∑ e ∈ UpperWholePayments.splitCells x, a i e * x e (some j) :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (ha i e) (hbox e (some j)).1)
  have hb : (∑ e ∈ UpperWholePayments.splitCells x, a i e * x e (some j)) ≤ delta := by
    apply le_trans _ (hloss i)
    exact Finset.sum_le_sum (fun e _ => mul_le_of_le_one_right (ha i e) (hbox e (some j)).2)
  constructor <;> linarith

theorem sparse_split_mass (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (hcount : (UpperWholePayments.splitCells x).card ≤ Fintype.card Agent ^ 2)
    (hsmall : ∀ i e, e ∈ UpperWholePayments.splitCells x → a i e ≤ eta) (i : Agent) :
    (∑ e ∈ UpperWholePayments.splitCells x, a i e) ≤ (Fintype.card Agent : ℝ)^2 * eta := by
  calc
    _ ≤ ∑ _e ∈ UpperWholePayments.splitCells x, eta := Finset.sum_le_sum (fun e he => hsmall i e he)
    _ = ((UpperWholePayments.splitCells x).card : ℝ) * eta := by simp
    _ ≤ (Fintype.card Agent : ℝ)^2 * eta := by
      apply mul_le_mul_of_nonneg_right _ heta
      exact_mod_cast hcount

theorem frozen_split_subset (initial x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ initial e c ∧ initial e c ≤ 1)
    (hfrozen : UpperFloating.Frozen (fun c : Cell × Option Agent => initial c.1 c.2)
      (fun c : Cell × Option Agent => x c.1 c.2)) :
    UpperWholePayments.splitCells x ⊆ UpperWholePayments.splitCells initial := by
  intro e he
  by_contra hn
  obtain ⟨c,hpos,hlt⟩ := (Finset.mem_filter.mp he).2
  have hc := UpperWholePayments.outside_split_integral initial hbox e hn c
  have hfix : x e c = initial e c := hfrozen (e,c) hc
  rcases hc with hc | hc <;> rw [hfix,hc] at hpos hlt <;> linarith

theorem floated_split_subset (a : Agent → Cell → ℝ)
    (initial : UpperFloating.PaymentCoord Agent Cell → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ c, initial (e,c) = 1) :
    UpperWholePayments.splitCells (fun e c => UpperFloating.select a initial (e,c)) ⊆
      UpperWholePayments.splitCells (fun e c => initial (e,c)) :=
  frozen_split_subset _ _ (fun e c => hbox (e,c)) (UpperFloating.select_spec a initial hbox hrow).2.2.2.1

end EnvyFreeResearch.Full.UpperShrinkCarve
