import EnvyFreeResearch.Full.UpperFloatingPayments

/-! Finite linear-algebra certificates for discrepancy-aware rounding.
Own moments remain exact; only discrepancy equations may be dropped. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperSparseFloating
open UpperFloatingStep UpperFloating
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]
abbrev Coord := Cell × Option Agent
abbrev Pair := Agent × Agent

def pairCoeff (a : Agent → Cell → ℝ) (ij : Pair (Agent := Agent))
    (c : Coord (Agent := Agent) (Cell := Cell)) : ℝ :=
  if c.2 = some ij.2 then a ij.1 c.1-a ij.2 c.1 else 0

def pairValue (a : Agent → Cell → ℝ) (x : Coord (Agent := Agent) (Cell := Cell) → ℝ)
    (ij : Pair (Agent := Agent)) : ℝ := ∑ c, pairCoeff a ij c*x c

def equations (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent))) :
    (Cell ⊕ (Agent ⊕ S)) → Coord (Agent := Agent) (Cell := Cell) → ℝ
  | .inl e, c => if c.1=e then 1 else 0
  | .inr (.inl j), c => if c.2=some j then a j c.1 else 0
  | .inr (.inr ij), c => pairCoeff a ij c

theorem cell_equation (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ) (e : Cell) :
    linearValue (equations a S) x (.inl e) = ∑ j, x (e,j) := by
  change linearValue (UpperFloating.coefficients a) x (.inl e) = _
  exact UpperFloating.cell_equation a x e

theorem own_equation (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ) (j : Agent) :
    linearValue (equations a S) x (.inr (.inl j)) = ∑ e, a j e*x (e,some j) := by
  change linearValue (UpperFloating.coefficients a) x (.inr (j,j)) = _
  exact UpperFloating.moment_equation a x j j

theorem pair_equation (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ) (ij : S) :
    linearValue (equations a S) x (.inr (.inr ij)) = pairValue a x ij := rfl

/-- Only split cell equations count toward the fractional rank. -/
theorem rank_bound (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ)
    (hkernel : NoFractionalKernel (equations a S) x) :
    (fractional x).card ≤ (splitCells x).card+Fintype.card Agent+S.card := by
  let reduced : (splitCells x ⊕ (Agent ⊕ S)) → Coord (Agent := Agent) (Cell := Cell) → ℝ :=
    fun r => equations a S (r.map Subtype.val id)
  have hr : ∀ d : Coord (Agent := Agent) (Cell := Cell) → ℝ,
      (∀ c, d c ≠ 0 → c ∈ fractional x) →
      (∀ r, linearValue reduced d r=0) → d=0 := by
    intro d hs hd
    apply hkernel d hs
    intro r
    cases r with
    | inl e =>
      by_cases he : e ∈ splitCells x
      · exact hd (.inl ⟨e,he⟩)
      · rw [cell_equation]
        exact Finset.sum_eq_zero (fun j _ => supported_zero_off_split x d hs e he j)
    | inr r => exact hd (.inr r)
  have h := supported_kernel_card_bound reduced (fractional x) hr
  simpa [Fintype.card_sum, add_assoc] using h

/-- If too many fractional variables remain, at least one discrepancy row
has small support. This is the rank/degree argument independent of geometry. -/
theorem sparse_row {Rows : Type*} [Fintype Rows]
    (k V C : ℕ) (hk : 0 < k) (hV : 4*k ≤ V)
    (hrank : V ≤ C+k+Fintype.card Rows) (hcells : 2*C ≤ V)
    (degree : Rows → ℕ) (hdegree : ∑ r, degree r ≤ k*V) :
    ∃ r, degree r ≤ 4*k := by
  have hp : V ≤ 4*Fintype.card Rows := by omega
  have hrows : 0 < Fintype.card Rows := by omega
  haveI : Nonempty Rows := Fintype.card_pos_iff.mp hrows
  by_contra h
  push_neg at h
  have hsum : (∑ _r : Rows, 4*k) < ∑ r, degree r :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => h r)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hmul := Nat.mul_le_mul_left k hp
  nlinarith

def FrozenReal (x y : Coord (Agent := Agent) (Cell := Cell) → ℝ) : Prop :=
  ∀ e j, x (e,some j)=0 ∨ x (e,some j)=1 → y (e,some j)=x (e,some j)

theorem FrozenReal.trans {x y z : Coord (Agent := Agent) (Cell := Cell) → ℝ}
    (hxy : FrozenReal x y) (hyz : FrozenReal y z) : FrozenReal x z := by
  intro e j h
  have he := hxy e j h
  have h' : y (e,some j)=0 ∨ y (e,some j)=1 := by rw [he]; exact h
  exact (hyz e j h').trans he

theorem frozen_real {x y : Coord (Agent := Agent) (Cell := Cell) → ℝ}
    (h : Frozen x y) : FrozenReal x y := fun e j hj => h (e,some j) hj

def support (a : Agent → Cell → ℝ) (x : Coord (Agent := Agent) (Cell := Cell) → ℝ)
    (ij : Pair (Agent := Agent)) : Finset (Coord (Agent := Agent) (Cell := Cell)) :=
  (fractional x).filter (fun c => pairCoeff a ij c ≠ 0)

/-- A dropped equation remains controlled through arbitrary later moves
and final rounding, provided zero/one real-color coordinates stay fixed.
The unused color is allowed to change at the final underpaying round. -/
theorem support_error (a : Agent → Cell → ℝ)
    (x y : Coord (Agent := Agent) (Cell := Cell) → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (hy : ∀ c, 0 ≤ y c ∧ y c ≤ 1)
    (hfrozen : FrozenReal x y) (ij : Pair (Agent := Agent)) (A : ℝ)
    (hA : 0 ≤ A) (hcoeff : ∀ c, |pairCoeff a ij c| ≤ A) :
    |pairValue a y ij-pairValue a x ij| ≤ (support a x ij).card*A := by
  have hzero (c : Coord (Agent := Agent) (Cell := Cell))
      (hc : c ∉ support a x ij) : pairCoeff a ij c*(y c-x c)=0 := by
    by_cases hd : pairCoeff a ij c=0
    · simp [hd]
    have hfrac : c ∉ fractional x := by
      intro h
      exact hc (Finset.mem_filter.mpr ⟨h,hd⟩)
    have hb : x c=0 ∨ x c=1 := by
      have h := hx c
      simp only [fractional, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hfrac
      by_cases h0 : x c=0
      · exact Or.inl h0
      · right
        have hp : 0 < x c := lt_of_le_of_ne h.1 (Ne.symm h0)
        have hn := hfrac hp
        linarith
    rcases c with ⟨e,j⟩
    cases j with
    | none => simp [pairCoeff] at hd
    | some j => simp [hfrozen e j hb]
  have heq : pairValue a y ij-pairValue a x ij =
      ∑ c ∈ support a x ij, pairCoeff a ij c*(y c-x c) := by
    unfold pairValue
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    exact hzero c hc
  rw [heq]
  calc
    _ ≤ ∑ c ∈ support a x ij, |pairCoeff a ij c*(y c-x c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ support a x ij, A := by
      apply Finset.sum_le_sum
      intro c _
      have habs : |y c-x c| ≤ 1 := abs_le.mpr ⟨by linarith [hx c,hy c],by linarith [hx c,hy c]⟩
      rw [abs_mul]
      exact (mul_le_mul (hcoeff c) habs (abs_nonneg _) hA).trans_eq (mul_one _)
    _ = _ := by simp

end EnvyFreeResearch.Full.RefinedUpperSparseFloating
