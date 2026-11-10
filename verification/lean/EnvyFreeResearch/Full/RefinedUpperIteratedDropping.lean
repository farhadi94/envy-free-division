import EnvyFreeResearch.Full.RefinedUpperSparseFloating

/-! Sparse discrepancy equations may be dropped, while owner equations and
cell sums remain exact. The final certificate controls every subsequent
support-preserving rounding, not just the current fractional table. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperSparseFloating
open UpperFloatingStep UpperFloating
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

lemma column_degree (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (c : Coord (Agent := Agent) (Cell := Cell)) :
    (S.filter (fun ij => pairCoeff a ij c ≠ 0)).card ≤ Fintype.card Agent := by
  let T := S.filter (fun ij => pairCoeff a ij c ≠ 0)
  have howner (ij : T) : c.2=some ij.val.2 := by
    have hn := (Finset.mem_filter.mp ij.property).2
    by_contra h
    simp [pairCoeff,h] at hn
  let f : T → Agent := fun ij => ij.val.1
  have hi : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext hpq
    exact Option.some.inj ((howner p).symm.trans (howner q))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

lemma sum_support (a : Agent → Cell → ℝ) (S : Finset (Pair (Agent := Agent)))
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ) :
    (∑ ij : S, (support a x ij).card) ≤ Fintype.card Agent*(fractional x).card := by
  rw [Finset.sum_coe_sort S (fun ij => (support a x ij).card)]
  calc
    _ = ∑ ij ∈ S, ∑ c ∈ fractional x, if pairCoeff a ij c ≠ 0 then 1 else 0 := by
      simp only [support,Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = ∑ c ∈ fractional x, ∑ ij ∈ S, if pairCoeff a ij c ≠ 0 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ c ∈ fractional x, (S.filter (fun ij => pairCoeff a ij c ≠ 0)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    _ ≤ ∑ _c ∈ fractional x, Fintype.card Agent :=
      Finset.sum_le_sum (fun c _ => column_degree a S c)
    _ = _ := by simp [Nat.mul_comm]

lemma frozen_trans {x y z : Coord (Agent := Agent) (Cell := Cell) → ℝ}
    (hxy : Frozen x y) (hyz : Frozen y z) : Frozen x z := by
  intro c hc
  have he := hxy c hc
  have h' : y c=0 ∨ y c=1 := by rw [he]; exact hc
  exact (hyz c h').trans he

/-- Every initial feasible table has a table with at most 4k fractional
coordinates, exact owner moments, and a robust 4k discrepancy certificate.
The latter remains true after the final supported whole-cell rounding. -/
theorem exists_robust_float (a : Agent → Cell → ℝ) (A : Pair (Agent := Agent) → ℝ)
    (hA : ∀ ij, 0 ≤ A ij)
    (hcoeff : ∀ ij c, |pairCoeff a ij c| ≤ A ij)
    (hk : 0 < Fintype.card Agent)
    (S : Finset (Pair (Agent := Agent)))
    (initial : Coord (Agent := Agent) (Cell := Cell) → ℝ)
    (hbox : ∀ c, 0 ≤ initial c ∧ initial c ≤ 1)
    (hrow : ∀ e, ∑ j, initial (e,j)=1) :
    ∃ y : Coord (Agent := Agent) (Cell := Cell) → ℝ,
      (∀ c, 0 ≤ y c ∧ y c ≤ 1) ∧ (∀ e, ∑ j, y (e,j)=1) ∧
      (∀ j, (∑ e, a j e*y (e,some j)) = ∑ e, a j e*initial (e,some j)) ∧
      Frozen initial y ∧ (fractional y).card ≤ 4*Fintype.card Agent ∧
      (∀ z, (∀ c, 0 ≤ z c ∧ z c ≤ 1) → FrozenReal y z → ∀ ij ∈ S,
        |pairValue a z ij-pairValue a initial ij| ≤ (4*Fintype.card Agent:ℕ)*A ij) := by
  suffices h : ∀ m : ℕ, ∀ S : Finset (Pair (Agent := Agent)), S.card=m →
      ∀ initial : Coord (Agent := Agent) (Cell := Cell) → ℝ,
      (∀ c, 0 ≤ initial c ∧ initial c ≤ 1) → (∀ e, ∑ j, initial (e,j)=1) →
      ∃ y : Coord (Agent := Agent) (Cell := Cell) → ℝ,
        (∀ c, 0 ≤ y c ∧ y c ≤ 1) ∧ (∀ e, ∑ j, y (e,j)=1) ∧
        (∀ j, (∑ e, a j e*y (e,some j)) = ∑ e, a j e*initial (e,some j)) ∧
        Frozen initial y ∧ (fractional y).card ≤ 4*Fintype.card Agent ∧
        (∀ z, (∀ c, 0 ≤ z c ∧ z c ≤ 1) → FrozenReal y z → ∀ ij ∈ S,
          |pairValue a z ij-pairValue a initial ij| ≤ (4*Fintype.card Agent:ℕ)*A ij) by
    exact h S.card S rfl initial hbox hrow
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hcard initial hbox hrow
    obtain ⟨x,hx,hkernel⟩ := exists_frozen_basic (equations a S)
      (linearValue (equations a S) initial) initial ⟨hbox,fun _ => rfl⟩
    have hxrow (e : Cell) : ∑ j, x (e,j)=1 := by
      rw [← cell_equation a S x e,hx.1.2,cell_equation,hrow]
    have hxown (j : Agent) : (∑ e, a j e*x (e,some j)) =
        ∑ e, a j e*initial (e,some j) := by
      rw [← own_equation a S x j,hx.1.2,own_equation]
    have hxpair (ij : Pair (Agent := Agent)) (hij : ij ∈ S) :
        pairValue a x ij=pairValue a initial ij :=
      hx.1.2 (.inr (.inr ⟨ij,hij⟩))
    by_cases hsmall : (fractional x).card ≤ 4*Fintype.card Agent
    · refine ⟨x,hx.1.1,hxrow,hxown,hx.2,hsmall,?_⟩
      intro z hz hf ij hij
      rw [← hxpair ij hij]
      have hb := support_error a x z hx.1.1 hz hf ij (A ij) (hA ij) (hcoeff ij)
      have hcount : (support a x ij).card ≤ 4*Fintype.card Agent :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans hsmall
      exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (hA ij))
    · have hrank := rank_bound a S x hkernel
      have htwo := twice_split_le_fractional x hx.1.1 hxrow
      obtain ⟨ij,hij⟩ := sparse_row (Rows := S) (Fintype.card Agent)
        (fractional x).card (splitCells x).card hk (by omega)
        (by simpa only [Fintype.card_coe] using hrank) htwo
        (fun r => (support a x r).card) (sum_support a S x)
      have hlt : (S.erase ij.val).card < m := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem ij.property
      obtain ⟨y,hybox,hyrow,hyown,hyfrozen,hycount,hyrobust⟩ :=
        ih (S.erase ij.val).card hlt (S.erase ij.val) rfl x hx.1.1 hxrow
      refine ⟨y,hybox,hyrow,fun j => (hyown j).trans (hxown j),
        frozen_trans hx.2 hyfrozen,hycount,?_⟩
      intro z hz hf r hr
      rw [← hxpair r hr]
      by_cases heq : r=ij.val
      · subst r
        have hfreeze := (frozen_real hyfrozen).trans hf
        have hb := support_error a x z hx.1.1 hz hfreeze ij (A ij) (hA ij) (hcoeff ij)
        exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (hA ij))
      · exact hyrobust z hz hf r (Finset.mem_erase.mpr ⟨heq,hr⟩)

end EnvyFreeResearch.Full.RefinedUpperSparseFloating
