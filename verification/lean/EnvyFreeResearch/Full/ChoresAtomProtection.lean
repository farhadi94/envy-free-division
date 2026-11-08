import EnvyFreeResearch.Full.ChoresPackageProposal
import EnvyFreeResearch.R5ChoreMatching

/-! Original-gap protection on literal measurable prefixes and suffixes.
An omitted observer's large original gap cannot fit in an all-small
offered suffix. Thus every allowed donor removal preserves that observer's
equalizer and creates zero actual deficit. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.AtomProtection
open Set MeasureTheory PackageGeometry
open scoped BigOperators

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

theorem prefix_suffix_cost (P : Set ℝ) (hP : MeasurableSet P) (x : ℝ) :
    μ.real (P ∩ Iic x)+μ.real (P ∩ Ioi x) = μ.real P := by
  have hd : Disjoint (P ∩ Iic x) (P ∩ Ioi x) :=
    disjoint_left.mpr (fun y hx hy =>
      not_lt_of_ge (show y ≤ x from hx.2) (show x < y from hy.2))
  have hu : (P ∩ Iic x) ∪ (P ∩ Ioi x) = P := by
    ext y
    simp only [mem_union,mem_inter_iff,mem_Iic,mem_Ioi]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_or_gt y x with hx | hx
      · exact Or.inl ⟨h,hx⟩
      · exact Or.inr ⟨h,hx⟩
  rw [← measureReal_union hd (hP.inter measurableSet_Ioi),hu]

theorem gap_is_suffix (P : Set ℝ) (hP : MeasurableSet P) (equalizer baseline : ℝ)
    (hvalue : μ.real (P ∩ Iic equalizer) = baseline) :
    μ.real P-baseline = μ.real (P ∩ Ioi equalizer) := by
  have h := prefix_suffix_cost μ P hP equalizer
  rw [hvalue] at h
  linarith

theorem suffix_antitone (P : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    P ∩ Ioi b ⊆ P ∩ Ioi a :=
  inter_subset_inter_right P (Ioi_subset_Ioi hab)

/-- The wrong-side contradiction is about actual original costs. It uses
the positive fixed reference cost and the strict separation H²>n. -/
theorem omitted_equalizer_protected (P : Set ℝ) (hP : MeasurableSet P)
    (equalizer frontier baseline r H n : ℝ)
    (hvalue : μ.real (P ∩ Iic equalizer) = baseline)
    (hr : 0 < r) (hH : 0 < H) (hscale : n < H*H)
    (hlarge : H*r ≤ μ.real P-baseline)
    (hsmall : μ.real (P ∩ Ioi frontier) ≤ n*r/H) : equalizer ≤ frontier := by
  by_contra h
  have horder : frontier ≤ equalizer := (lt_of_not_ge h).le
  have hgap : μ.real P-baseline ≤ n*r/H := by
    rw [gap_is_suffix μ P hP equalizer baseline hvalue]
    exact (measureReal_mono (μ := μ) (suffix_antitone P horder)).trans hsmall
  exact R5ChoreMatching.omitted_mark_contradiction n r H (μ.real P-baseline)
    hr hH hscale hlarge hgap

theorem equalizer_retained (P removed : Set ℝ) {equalizer frontier : ℝ}
    (horder : equalizer ≤ frontier) (hremoved : removed ⊆ P ∩ Ioi frontier) :
    P ∩ Iic equalizer ⊆ P \ removed := by
  intro x hx
  refine ⟨hx.1,?_⟩
  intro hD
  exact not_lt_of_ge (hx.2.trans horder) (hremoved hD).2

theorem protected_cost (P removed : Set ℝ) (equalizer frontier baseline : ℝ)
    (horder : equalizer ≤ frontier) (hremoved : removed ⊆ P ∩ Ioi frontier)
    (hvalue : μ.real (P ∩ Iic equalizer) = baseline) :
    baseline ≤ μ.real (P \ removed) := by
  rw [← hvalue]
  exact measureReal_mono (equalizer_retained P removed horder hremoved)

theorem protected_deficit_zero (P removed : Set ℝ) (equalizer frontier baseline : ℝ)
    (horder : equalizer ≤ frontier) (hremoved : removed ⊆ P ∩ Ioi frontier)
    (hvalue : μ.real (P ∩ Iic equalizer) = baseline) :
    max 0 (baseline-μ.real (P \ removed)) = 0 :=
  max_eq_left (sub_nonpos.mpr (protected_cost μ P removed equalizer frontier baseline horder hremoved hvalue))

theorem protected_masked_utility_zero (P removed : Set ℝ) (hP : MeasurableSet P)
    (equalizer frontier baseline : ℝ) (horder : equalizer ≤ frontier)
    (hremoved : removed ⊆ P ∩ Ioi frontier)
    (hvalue : μ.real (P ∩ Iic equalizer) = baseline) :
    max 0 (μ.real removed-(μ.real P-baseline)) = 0 := by
  apply max_eq_left
  apply sub_nonpos.mpr
  rw [gap_is_suffix μ P hP equalizer baseline hvalue]
  exact measureReal_mono (hremoved.trans (suffix_antitone P horder))

/-- The all-small suffix bound is derived by counting the actual original
atom sets. They need not be individual physical interval components. -/
theorem small_atoms_bound {Atom : Type*} [Fintype Atom]
    (suffix : Set ℝ) (atoms : Atom → Set ℝ) (r H : ℝ)
    (hsupport : suffix ⊆ ⋃ a, atoms a)
    (hsmall : ∀ a, μ.real (atoms a) ≤ r/H) :
    μ.real suffix ≤ (Fintype.card Atom : ℝ)*r/H := by
  calc
    μ.real suffix ≤ μ.real (⋃ a, atoms a) := measureReal_mono hsupport
    _ ≤ ∑ a, μ.real (atoms a) := measureReal_iUnion_fintype_le atoms
    _ ≤ ∑ _a : Atom, r/H := Finset.sum_le_sum (fun a _ => hsmall a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end EnvyFreeResearch.Full.Chores.AtomProtection
