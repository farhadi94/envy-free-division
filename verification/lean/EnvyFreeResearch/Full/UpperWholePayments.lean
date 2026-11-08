import EnvyFreeResearch.Full.UpperRoundingMeasurable

/-!
# Restoring the fixed integral payments

Apply the proved deterministic rounding selector only to split cells, clip
its output to those cells, and restore the original integral coordinates.
The resulting whole-cell payments are disjoint, underpay their owners by
at most one cell, and change each observer difference only on split cells.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperWholePayments

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def splitCells (x : Cell → Option Agent → ℝ) : Finset Cell :=
  Finset.univ.filter (fun e => ∃ c, 0 < x e c ∧ x e c < 1)

def integralCells (x : Cell → Option Agent → ℝ) (j : Agent) : Finset Cell :=
  Finset.univ.filter (fun e => x e (some j) = 1)

def splitValues (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ) :
    Agent → Cell → ℝ := fun i e => if e ∈ splitCells x then a i e else 0

def splitFractions (x : Cell → Option Agent → ℝ) : Agent → Cell → ℝ :=
  fun j e => if e ∈ splitCells x then x e (some j) else 0

def splitOwned (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (j : Agent) : Finset Cell :=
  (UpperRounding.select (splitValues a x) (splitFractions x) eta j).filter
    (fun e => e ∈ splitCells x)

def owned (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (j : Agent) : Finset Cell := integralCells x j ∪ splitOwned a x eta j

def value (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (i j : Agent) : ℝ := ∑ e ∈ owned a x eta j, a i e

def fractionalValue (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (i j : Agent) : ℝ := ∑ e, a i e * x e (some j)

omit [Fintype Cell] in
theorem other_coordinate_zero (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (e : Cell) (c d : Option Agent)
    (hc : x e c = 1) (hcd : d ≠ c) : x e d = 0 := by
  have hdmem : d ∈ (Finset.univ : Finset (Option Agent)).erase c := by simp [hcd]
  have hd := Finset.single_le_sum (s := Finset.univ.erase c) (f := x e)
    (fun z _ => (hbox e z).1) hdmem
  have heq := Finset.sum_erase_add (s := Finset.univ) (f := x e) (by simp : c ∈ Finset.univ)
  rw [hsum, hc] at heq
  exact le_antisymm (by linarith) (hbox e d).1

theorem integral_not_split (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (j : Agent) (e : Cell)
    (he : e ∈ integralCells x j) : e ∉ splitCells x := by
  have hj : x e (some j) = 1 := (Finset.mem_filter.mp he).2
  simp only [splitCells, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨c, hpos, hlt⟩
  by_cases hc : c = some j
  · subst c
    linarith
  · have hz := other_coordinate_zero x hbox hsum e (some j) c hj hc
    linarith

theorem integral_disjoint (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (i j : Agent) (hij : i ≠ j) :
    Disjoint (integralCells x i) (integralCells x j) := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  have hei : x e (some i) = 1 := (Finset.mem_filter.mp hi).2
  have hej : x e (some j) = 1 := (Finset.mem_filter.mp hj).2
  have hz := other_coordinate_zero x hbox hsum e (some i) (some j) hei
    (by simpa using Ne.symm hij)
  linarith

theorem outside_split_integral (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (e : Cell)
    (he : e ∉ splitCells x) (c : Option Agent) : x e c = 0 ∨ x e c = 1 := by
  by_contra hn
  push Not at hn
  have hpos : 0 < x e c := lt_of_le_of_ne (hbox e c).1 (Ne.symm hn.1)
  have hlt : x e c < 1 := lt_of_le_of_ne (hbox e c).2 hn.2
  exact he (by simp [splitCells]; exact ⟨c, hpos, hlt⟩)

theorem splitFractions_nonneg (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (j : Agent) (e : Cell) :
    0 ≤ splitFractions x j e := by
  unfold splitFractions
  split_ifs <;> first | exact (hbox e (some j)).1 | exact le_rfl

theorem splitFractions_capacity (x : Cell → Option Agent → ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (e : Cell) :
    ∑ j, splitFractions x j e ≤ 1 := by
  by_cases he : e ∈ splitCells x
  · simp only [splitFractions, ite_eq_left he]
    have h := hsum e
    rw [Fintype.sum_option] at h
    linarith [(hbox e none).1]
  · simp [splitFractions, he]

theorem split_rounding_spec (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e)
    (hsmall : ∀ i e, a i e ≤ eta)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) :
    UpperRounding.Valid (splitValues a x) (splitFractions x) eta
      (UpperRounding.select (splitValues a x) (splitFractions x) eta) := by
  apply UpperRounding.select_spec _ _ _ heta
  · intro i e
    dsimp [splitValues]
    split_ifs <;> first | exact ha i e | exact le_rfl
  · intro i e
    dsimp [splitValues]
    split_ifs <;> first | exact hsmall i e | exact heta
  · exact splitFractions_nonneg x hbox
  · exact splitFractions_capacity x hbox hsum

theorem splitOwned_load (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (i j : Agent) :
    (∑ e ∈ splitOwned a x eta j, a i e) =
      ∑ e ∈ UpperRounding.select (splitValues a x) (splitFractions x) eta j,
        splitValues a x i e := by
  simp only [splitOwned, Finset.sum_filter, splitValues]

theorem split_target (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ) (j : Agent) :
    UpperRounding.target (splitValues a x) (splitFractions x) j =
      ∑ e ∈ splitCells x, a j e * x e (some j) := by
  simp only [UpperRounding.target, splitValues, splitFractions]
  calc
    _ = ∑ e, if e ∈ splitCells x then a j e * x e (some j) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem integral_splitOwned_disjoint (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (i j : Agent) :
    Disjoint (integralCells x i) (splitOwned a x eta j) := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  exact integral_not_split x hbox hsum i e hi (Finset.mem_filter.mp hj).2

theorem owned_disjoint (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e)
    (hsmall : ∀ i e, a i e ≤ eta)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (i j : Agent) (hij : i ≠ j) :
    Disjoint (owned a x eta i) (owned a x eta j) := by
  rw [owned, owned, Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  refine ⟨⟨integral_disjoint x hbox hsum i j hij,
    integral_splitOwned_disjoint a x eta hbox hsum i j⟩, ?_, ?_⟩
  · exact (integral_splitOwned_disjoint a x eta hbox hsum j i).symm
  · exact ((split_rounding_spec a x eta heta ha hsmall hbox hsum).1 i j hij).mono
      (Finset.filter_subset ..) (Finset.filter_subset ..)

theorem fractional_decomposition (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (i j : Agent) :
    fractionalValue a x i j = (∑ e ∈ integralCells x j, a i e) +
      ∑ e ∈ splitCells x, a i e * x e (some j) := by
  simp only [fractionalValue, integralCells, splitCells, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : x e (some j) = 1
  · have hns := integral_not_split x hbox hsum j e (by simp [integralCells, hi])
    have hns' : ¬ ∃ c, 0 < x e c ∧ x e c < 1 := by simpa [splitCells] using hns
    simp [hi, hns']
  · by_cases hs : e ∈ splitCells x
    · simp only [ite_eq_right hi]
      simp [splitCells] at hs
      simp [hs]
    · have hz := (outside_split_integral x hbox e hs (some j)).resolve_right hi
      simp only [ite_eq_right hi]
      have hns : ¬ ∃ c, 0 < x e c ∧ x e c < 1 := by simpa [splitCells] using hs
      simp [hz, hns]

theorem owner_deficit (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e)
    (hsmall : ∀ i e, a i e ≤ eta)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1)
    (hsum : ∀ e, ∑ c, x e c = 1) (j : Agent) :
    0 ≤ fractionalValue a x j j - value a x eta j j ∧
      fractionalValue a x j j - value a x eta j j ≤ min (fractionalValue a x j j) eta := by
  have hr := (split_rounding_spec a x eta heta ha hsmall hbox hsum).2 j
  rw [split_target, UpperRounding.load, ← splitOwned_load] at hr
  have hdec := fractional_decomposition a x hbox hsum j j
  have hv : value a x eta j j = (∑ e ∈ integralCells x j, a j e) +
      ∑ e ∈ splitOwned a x eta j, a j e := by
    exact Finset.sum_union (integral_splitOwned_disjoint a x eta hbox hsum j j)
  have hnonneg : 0 ≤ value a x eta j j := Finset.sum_nonneg (fun e _ => ha j e)
  refine ⟨by linarith, le_min (by linarith) (by linarith)⟩

def changeCoefficient (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (j : Agent) (e : Cell) : ℝ :=
  (if e ∈ owned a x eta j then 1 else 0) - x e (some j)

theorem changeCoefficient_abs_le_one (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (j : Agent) (e : Cell) :
    |changeCoefficient a x eta j e| ≤ 1 := by
  dsimp [changeCoefficient]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [hbox e (some j)]

theorem changeCoefficient_zero_outside (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (j : Agent) (e : Cell)
    (he : e ∉ splitCells x) : changeCoefficient a x eta j e = 0 := by
  have hs : e ∉ splitOwned a x eta j := by simp [splitOwned, he]
  rcases outside_split_integral x hbox e he (some j) with hz | ho
  · simp [changeCoefficient, owned, integralCells, hz, hs]
  · simp [changeCoefficient, owned, integralCells, ho]

theorem value_sub_fractional (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ) (i j : Agent) :
    value a x eta i j - fractionalValue a x i j =
      ∑ e, a i e * changeCoefficient a x eta j e := by
  have hv : value a x eta i j = ∑ e, if e ∈ owned a x eta j then a i e else 0 := by
    simp only [value, Finset.sum_ite_mem_eq]
  rw [hv, fractionalValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  dsimp [changeCoefficient]
  split_ifs <;> ring

theorem disagreement_identity (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (i j : Agent) :
    value a x eta i j - value a x eta j j -
      (fractionalValue a x i j - fractionalValue a x j j) =
      ∑ e ∈ splitCells x, (a i e - a j e) * changeCoefficient a x eta j e := by
  calc
    _ = (value a x eta i j - fractionalValue a x i j) -
        (value a x eta j j - fractionalValue a x j j) := by ring
    _ = ∑ e, (a i e - a j e) * changeCoefficient a x eta j e := by
      rw [value_sub_fractional, value_sub_fractional, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro e _ he
      rw [changeCoefficient_zero_outside a x eta hbox j e he, mul_zero]

/-- All fixed cells contribute exactly their original moment. Each split
cell changes its coefficient by at most one, including cells rounded to
the unused color. -/
theorem disagreement_bound (a : Agent → Cell → ℝ)
    (x : Cell → Option Agent → ℝ) (eta A : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (i j : Agent)
    (hA : 0 ≤ A) (hgap : ∀ e ∈ splitCells x, |a i e - a j e| ≤ A)
    (hmoment : fractionalValue a x i j = fractionalValue a x j j) :
    |value a x eta i j - value a x eta j j| ≤ (splitCells x).card * A := by
  have hid := disagreement_identity a x eta hbox i j
  rw [hmoment, sub_self, sub_zero] at hid
  rw [hid]
  calc
    _ ≤ ∑ e ∈ splitCells x, |(a i e - a j e) * changeCoefficient a x eta j e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ splitCells x, A := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      calc
        _ ≤ A * 1 := mul_le_mul (hgap e he)
          (changeCoefficient_abs_le_one a x eta hbox j e) (abs_nonneg _) hA
        _ = A := mul_one _
    _ = _ := by simp

/-- The complete cached whole-payment guarantee, using the independently
proved bound on the number of split cells as its explicit input. -/
theorem whole_payment_bounds (a : Agent → Cell → ℝ) (x : Cell → Option Agent → ℝ)
    (eta : ℝ) (t : Agent → ℝ) (A : Agent → Agent → ℝ)
    (heta : 0 ≤ eta) (ha : ∀ i e, 0 ≤ a i e) (hsmall : ∀ i e, a i e ≤ eta)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hsum : ∀ e, ∑ c, x e c = 1)
    (hmoment : ∀ i j, fractionalValue a x i j = t j)
    (hA : ∀ i j, 0 ≤ A i j) (hgap : ∀ i j e, |a i e - a j e| ≤ A i j)
    (hcount : (splitCells x).card ≤ Fintype.card Agent ^ 2) :
    (∀ j, 0 ≤ t j - value a x eta j j ∧ t j - value a x eta j j ≤ min (t j) eta) ∧
      (∑ j : Agent, (t j - value a x eta j j)) ≤ Fintype.card Agent * eta ∧
      ∀ i j, |value a x eta i j - value a x eta j j| ≤
        (Fintype.card Agent : ℝ) ^ 2 * A i j := by
  have hdef (j : Agent) := owner_deficit a x eta heta ha hsmall hbox hsum j
  simp only [hmoment] at hdef
  refine ⟨hdef, ?_, ?_⟩
  · calc
      _ ≤ ∑ _j : Agent, eta := Finset.sum_le_sum (fun j _ => (hdef j).2.trans (min_le_right ..))
      _ = _ := by simp
  · intro i j
    have h := disagreement_bound a x eta (A i j) hbox i j (hA i j)
      (fun e _ => hgap i j e) ((hmoment i j).trans (hmoment j j).symm)
    have hc : ((splitCells x).card : ℝ) ≤ (Fintype.card Agent : ℝ) ^ 2 := by
      exact_mod_cast hcount
    exact h.trans (mul_le_mul_of_nonneg_right hc (hA i j))

end EnvyFreeResearch.Full.UpperWholePayments
