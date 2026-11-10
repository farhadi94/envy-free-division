import EnvyFreeResearch.Full.RefinedUpperIteratedDropping
import EnvyFreeResearch.Full.RefinedUpperWholePayments
import EnvyFreeResearch.Full.UpperFloating

/-! Whole-cell payments with linear, rather than quadratic, discrepancy.
The result includes disjointness and the exact one-cell owner-deficit bounds.
It is uniform over all normalized finite nonnegative value tables. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperWholeLinear
open UpperFloatingStep UpperFloating RefinedUpperSparseFloating
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def load (a : Agent → Cell → ℝ) (owned : Agent → Finset Cell) (i j : Agent) : ℝ :=
  ∑ e ∈ owned j, a i e

lemma owned_positive (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hsum : ∀ e, ∑ c, x e c=1)
    (j : Agent) (e : Cell) (he : e ∈ RefinedUpperWholePayments.owned a x eta j) :
    0 < x e (some j) := by
  open RefinedUpperWholePayments in
  have hs := RefinedUpperSupportedSelector.select_full_spec
    (splitValues a x) (splitFractions x) eta heta
    (by intro i e; unfold splitValues; split_ifs <;> first | exact ha i e | exact le_rfl)
    (by intro i e; unfold splitValues; split_ifs <;> first | exact hsmall i e | exact heta)
    (splitFractions_nonneg x hbox) (splitFractions_capacity x hbox hsum)
  rcases Finset.mem_union.mp he with hi|hi
  · have hh := (Finset.mem_filter.mp hi).2
    linarith
  · have hm := Finset.mem_filter.mp hi
    have hp := hs.2 j e hm.1
    simpa only [RefinedUpperWholePayments.splitFractions,hm.2,ite_true] using hp

lemma pairValue_formula (a : Agent → Cell → ℝ)
    (x : Coord (Agent := Agent) (Cell := Cell) → ℝ) (i j : Agent) :
    pairValue a x (i,j) = ∑ e, (a i e-a j e)*x (e,some j) := by
  simp [pairValue,pairCoeff,Fintype.sum_prod_type]

/-- The improved whole-cell payment lemma used by reserve-free Repair.
It does not assume a sparse fractional plan or a discrepancy certificate:
both are constructed by the iterated-dropping theorem. -/
theorem exists_whole_payments (a : Agent → Cell → ℝ) (t : Agent → ℝ)
    (A : Agent → Agent → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hnormal : ∀ i, ∑ e, a i e=1) (ht : ∀ j, 0 ≤ t j) (htsum : ∑ j, t j ≤ 1)
    (hA : ∀ i j, 0 ≤ A i j) (hgap : ∀ i j e, |a i e-a j e| ≤ A i j)
    (hk : 0 < Fintype.card Agent) :
    ∃ owned : Agent → Finset Cell,
      (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
      (∀ j, 0 ≤ t j-load a owned j j ∧ t j-load a owned j j ≤ min (t j) eta) ∧
      (∀ i j, |load a owned i j-load a owned j j| ≤ 4*(Fintype.card Agent:ℝ)*A i j) := by
  have hc : ∀ ij : Pair (Agent := Agent), ∀ c : Coord (Agent := Agent) (Cell := Cell),
      |pairCoeff a ij c| ≤ A ij.1 ij.2 := by
    intro ij c
    unfold pairCoeff
    split_ifs
    · exact hgap _ _ _
    · simpa using hA ij.1 ij.2
  obtain ⟨y,hybox,hyrow,hyown,_,_,hyrobust⟩ := exists_robust_float a
    (fun ij => A ij.1 ij.2) (fun ij => hA ij.1 ij.2) hc hk Finset.univ
    (commonPlan t) (commonPlan_box t ht htsum) (commonPlan_row t)
  let x : Cell → Option Agent → ℝ := fun e j => y (e,j)
  let owned := RefinedUpperWholePayments.owned a x eta
  let z : Coord (Agent := Agent) (Cell := Cell) → ℝ := fun c =>
    match c.2 with
    | none => 0
    | some j => if c.1 ∈ owned j then 1 else 0
  have hz : ∀ c, 0 ≤ z c ∧ z c ≤ 1 := by
    rintro ⟨e,j⟩
    cases j with
    | none => norm_num [z]
    | some j => dsimp [z]; split_ifs <;> norm_num
  have hf : FrozenReal y z := by
    intro e j hj
    rcases hj with hzero|hone
    · have hnot : e ∉ owned j := by
        intro he
        have hp := owned_positive a x eta heta ha hsmall
          (fun e c => hybox (e,c)) hyrow j e he
        change 0 < y (e,some j) at hp
        linarith
      simp [z,hnot,hzero]
    · have hmem : e ∈ owned j := by
        apply Finset.mem_union_left
        simp [RefinedUpperWholePayments.integralCells,x,hone]
      simp [z,hmem,hone]
  have hztarget (j : Agent) : RefinedUpperWholePayments.fractionalValue a x j j=t j := by
    exact (hyown j).trans (commonPlan_moment a t hnormal j j)
  have hzero (i j : Agent) : pairValue a (commonPlan t) (i,j)=0 := by
    rw [pairValue_formula]
    simp only [commonPlan]
    rw [← Finset.sum_mul,Finset.sum_sub_distrib,hnormal,hnormal]
    ring
  have hzvalue (i j : Agent) : pairValue a z (i,j)=load a owned i j-load a owned j j := by
    rw [pairValue_formula]
    simp only [z,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_ite_mem_eq,Finset.sum_sub_distrib]
    rfl
  refine ⟨owned,RefinedUpperWholePayments.owned_disjoint a x eta heta ha hsmall
    (fun e c => hybox (e,c)) hyrow,?_,?_⟩
  · intro j
    have h := RefinedUpperWholePayments.owner_deficit a x eta heta ha hsmall
      (fun e c => hybox (e,c)) hyrow j
    rw [hztarget] at h
    exact h
  · intro i j
    have h := hyrobust z hz hf (i,j) (Finset.mem_univ _)
    rw [hzero,sub_zero,hzvalue] at h
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end EnvyFreeResearch.Full.RefinedUpperWholeLinear
