import EnvyFreeResearch.NearExact
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Finite certificates for adaptive refinement and safe-scale completion

This module checks counting, rounding, geometric-scale separation, and bracket
algebra. It does not axiomatize or formalize a linear program, a physical Cut
oracle, a probability law, or the complete allocation protocol.
-/

namespace EnvyFreeResearch.R3Refinement

open scoped BigOperators

/-- In a nonnegative color vector summing to one, one strictly fractional
coordinate forces at least two strictly fractional coordinates. -/
theorem fractional_row_has_two_variables {Color : Type*} [Fintype Color]
    (x : Color → ℝ) (hnonneg : ∀ c, 0 ≤ x c) (hsum : ∑ c, x c = 1)
    (c : Color) (hc : 0 < x c ∧ x c < 1) :
    2 ≤ (Finset.univ.filter (fun d => 0 < x d ∧ x d < 1)).card := by
  classical
  have hother : ∃ d, d ≠ c ∧ 0 < x d := by
    by_contra hn
    push Not at hn
    have hsingle : (∑ d, x d) = x c := by
      apply Finset.sum_eq_single c
      · intro d _ hdc
        exact le_antisymm (hn d hdc) (hnonneg d)
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ c))
    linarith [hc.2]
  obtain ⟨d, hdc, hdpos⟩ := hother
  have hpair : x c + x d ≤ 1 := by
    have hsub : (∑ e ∈ ({c, d} : Finset Color), x e) ≤ ∑ e, x e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      exact hnonneg e
    simpa [hdc.symm, hsum] using hsub
  have hdupper : x d < 1 := by linarith [hc.1]
  apply Finset.one_lt_card.mpr
  exact ⟨c, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc,
    d, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hdpos, hdupper⟩,
    hdc.symm⟩

/-- The rank-budget arithmetic, with natural-number subtraction at K=0 or K=1. -/
theorem sparse_count (q p r K : ℕ) (htwo : 2 * q ≤ p)
    (hrank : p ≤ q + r * (K - 1)) : q ≤ r * (K - 1) := by omega

/-- Derive the fractional-cell bound from actual finite variable-support counts.
The independent-equation/rank bound remains an explicit external certificate. -/
theorem sparse_fractional_atom_bound {Cell Color : Type*}
    (fractional : Finset Cell) (support : Cell → Finset Color) (r K : ℕ)
    (htwo : ∀ a ∈ fractional, 2 ≤ (support a).card)
    (hrank : (∑ a ∈ fractional, (support a).card) ≤
      fractional.card + r * (K - 1)) : fractional.card ≤ r * (K - 1) := by
  apply sparse_count fractional.card (∑ a ∈ fractional, (support a).card) r K _ hrank
  calc
    2 * fractional.card = ∑ _a ∈ fractional, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ fractional, (support a).card := Finset.sum_le_sum htwo

theorem residual_mass_bound {Cell : Type*} (fractional : Finset Cell)
    (mass : Cell → ℝ) (ε : ℝ) (B : ℕ)
    (hε : 0 ≤ ε) (hcount : fractional.card ≤ B)
    (hsmall : ∀ a ∈ fractional, mass a ≤ ε) :
    (∑ a ∈ fractional, mass a) ≤ (B : ℝ) * ε := by
  calc
    (∑ a ∈ fractional, mass a) ≤ ∑ _a ∈ fractional, ε := Finset.sum_le_sum hsmall
    _ = (fractional.card : ℝ) * ε := by simp
    _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hε

/-- Sending every residual fractional cell to a dummy loses at most its total
mass from each real color, and can never overshoot that color's target. -/
theorem one_sided_dummy_rounding {Cell : Type*}
    (fractional : Finset Cell) (mass fraction : Cell → ℝ) (kept target δ : ℝ)
    (hmass : ∀ a ∈ fractional, 0 ≤ mass a)
    (hfraction : ∀ a ∈ fractional, 0 ≤ fraction a ∧ fraction a ≤ 1)
    (hresidual : (∑ a ∈ fractional, mass a) ≤ δ)
    (hconserved : target = kept + ∑ a ∈ fractional, mass a * fraction a) :
    target - δ ≤ kept ∧ kept ≤ target := by
  have hlo : 0 ≤ ∑ a ∈ fractional, mass a * fraction a := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hmass a ha) (hfraction a ha).1
  have hhi : (∑ a ∈ fractional, mass a * fraction a) ≤ δ := by
    apply le_trans _ hresidual
    apply Finset.sum_le_sum
    intro a ha
    simpa using mul_le_mul_of_nonneg_left (hfraction a ha).2 (hmass a ha)
  constructor <;> linarith

/-- A designated-cutter ending may repartition the whole residual pool: any
actual and target color amounts within that pool differ by at most its mass. -/
theorem pooled_rounding_error (actual target pool δ : ℝ)
    (ha : 0 ≤ actual ∧ actual ≤ pool) (ht : 0 ≤ target ∧ target ≤ pool)
    (hpool : pool ≤ δ) : |actual - target| ≤ δ := by
  apply abs_le.mpr
  constructor <;> linarith

/-- A row dropped when at most 2r variables remain fractional acquires error
at most 2rη, provided frozen variables never change and all coefficients are small. -/
theorem dropped_row_error {Variable : Type*} [Fintype Variable] [DecidableEq Variable]
    (live : Finset Variable) (coefficient before after : Variable → ℝ) (r : ℕ) (η : ℝ)
    (hη : 0 ≤ η) (hcount : live.card ≤ 2 * r)
    (hcoefficient : ∀ a ∈ live, 0 ≤ coefficient a ∧ coefficient a ≤ η)
    (hbefore : ∀ a ∈ live, 0 ≤ before a ∧ before a ≤ 1)
    (hafter : ∀ a ∈ live, 0 ≤ after a ∧ after a ≤ 1)
    (hfrozen : ∀ a ∉ live, after a = before a) :
    |(∑ a, coefficient a * after a) - (∑ a, coefficient a * before a)| ≤
      ((2 * r : ℕ) : ℝ) * η := by
  apply NearExact.finite_error_bound_of_card_le live
    (fun a => coefficient a * after a) (fun a => coefficient a * before a)
    η (2 * r) hη hcount
  · intro a ha
    have hb := hbefore a ha
    have hc := hcoefficient a ha
    have hafter0 : 0 ≤ coefficient a * after a := mul_nonneg hc.1 (hafter a ha).1
    have hafter1 : coefficient a * after a ≤ coefficient a := by
      simpa using mul_le_mul_of_nonneg_left (hafter a ha).2 hc.1
    simpa only [mul_comm (before a) (coefficient a)] using
      NearExact.one_cell_rounding_error (coefficient a) (coefficient a * after a)
        (before a) η hc.1 hc.2 hafter0 hafter1 hb.1 hb.2
  · intro a ha
    rw [hfrozen a ha]

section Pigeonhole

variable {Row Scale : Type*} [Fintype Row] [Fintype Scale]

/-- With at least as many scales as rows, one harmless row and at most one
forbidden scale per other row leave a scale safe for every row. -/
theorem exists_safe_scale (diagonal : Row) (forbidden : Row → Scale → Prop)
    (hdiagonal : ∀ l, ¬ forbidden diagonal l)
    (hunique : ∀ i a b, forbidden i a → forbidden i b → a = b)
    (hcard : Fintype.card Row ≤ Fintype.card Scale) :
    ∃ l, ∀ i, ¬ forbidden i l := by
  classical
  by_contra hnone
  push Not at hnone
  choose blocker hblocker using hnone
  have hne : ∀ l, blocker l ≠ diagonal := by
    intro l heq
    exact hdiagonal l (heq ▸ hblocker l)
  let f : Scale → {i : Row // i ≠ diagonal} := fun l => ⟨blocker l, hne l⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : blocker a = blocker b := congrArg Subtype.val hab
    exact hunique (blocker a) a b (hblocker a) (heq ▸ hblocker b)
  have hle := Fintype.card_le_of_injective f hinj
  have hlt : Fintype.card {i : Row // i ≠ diagonal} < Fintype.card Row :=
    Fintype.card_subtype_lt (x := diagonal) (by simp)
  omega

end Pigeonhole

noncomputable def geometricScale (τ θ : ℝ) (l : ℕ) : ℝ :=
  (2 / θ) * (8 / τ) ^ l

def Forbidden (τ G x : ℝ) : Prop := 3 * τ / 8 < G * x ∧ G * x < 2

theorem scale_positive (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 < θ) (l : ℕ) :
    0 < geometricScale τ θ l := by
  unfold geometricScale
  positivity

theorem scale_ratio_ge_one (τ : ℝ) (hτ : 0 < τ) (hτone : τ < 1) :
    1 ≤ 8 / τ := by
  apply (le_div_iff₀ hτ).mpr
  linarith

theorem scale_ge_base (τ θ : ℝ) (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ)
    (l : ℕ) : 2 / θ ≤ geometricScale τ θ l := by
  have hp : 1 ≤ (8 / τ) ^ l := one_le_pow₀ (scale_ratio_ge_one τ hτ hτone)
  have hbase : 0 ≤ 2 / θ := by positivity
  simpa only [geometricScale, mul_one] using mul_le_mul_of_nonneg_left hp hbase

/-- The full Shrink interface requires G≥1; θ≤2 suffices for every listed scale. -/
theorem scale_ge_one (τ θ : ℝ) (hτ : 0 < τ) (hτone : τ < 1)
    (hθ : 0 < θ) (hθtwo : θ ≤ 2) (l : ℕ) : 1 ≤ geometricScale τ θ l := by
  apply le_trans _ (scale_ge_base τ θ hτ hτone hθ l)
  apply (le_div_iff₀ hθ).mpr
  simpa using hθtwo

theorem later_scale_ge_ratio (τ θ : ℝ) (hτ : 0 < τ) (hτone : τ < 1)
    (hθ : 0 < θ) (a b : ℕ) (hab : a < b) :
    (8 / τ) * geometricScale τ θ a ≤ geometricScale τ θ b := by
  have hp : (8 / τ) ^ (a + 1) ≤ (8 / τ) ^ b :=
    pow_le_pow_right₀ (scale_ratio_ge_one τ hτ hτone) (by omega)
  calc
    (8 / τ) * geometricScale τ θ a = (2 / θ) * (8 / τ) ^ (a + 1) := by
      simp only [geometricScale, pow_succ]
      ring
    _ ≤ (2 / θ) * (8 / τ) ^ b := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = geometricScale τ θ b := rfl

/-- Once a positive ratio lies in the forbidden interval, every later listed
scale puts it above the interval. The constants give 3>2, including endpoint slack. -/
theorem later_scale_not_forbidden (τ θ x : ℝ)
    (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ) (hx : 0 ≤ x)
    (a b : ℕ) (hab : a < b) (hbad : Forbidden τ (geometricScale τ θ a) x) :
    ¬ Forbidden τ (geometricScale τ θ b) x := by
  intro hbadb
  have hratio := later_scale_ge_ratio τ θ hτ hτone hθ a b hab
  have hratio_x := mul_le_mul_of_nonneg_right hratio hx
  have hR : 0 < 8 / τ := by positivity
  have hlarge := mul_lt_mul_of_pos_left hbad.1 hR
  have hendpoint : (8 / τ) * (3 * τ / 8) = (3 : ℝ) := by
    field_simp
  rw [hendpoint] at hlarge
  dsimp [Forbidden] at hbadb
  nlinarith

theorem forbidden_scale_unique (τ θ x : ℝ)
    (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ) (hx : 0 ≤ x)
    (a b : ℕ) (ha : Forbidden τ (geometricScale τ θ a) x)
    (hb : Forbidden τ (geometricScale τ θ b) x) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (later_scale_not_forbidden τ θ x hτ hτone hθ hx a b hab ha hb)
  · exact hab
  · exact False.elim (later_scale_not_forbidden τ θ x hτ hτone hθ hx b a hab hb ha)

/-- A fully instantiated k-scale theorem, not a pigeonhole hypothesis about
an unspecified family: the powers and forbidden intervals are the actual proposed ones. -/
theorem exists_safe_geometric_scale {k : ℕ} (diagonal : Fin k)
    (τ θ : ℝ) (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ)
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) (hdiag : x diagonal = 0) :
    ∃ l : Fin k, ∀ i, geometricScale τ θ l.val * x i ≤ 3 * τ / 8 ∨
      2 ≤ geometricScale τ θ l.val * x i := by
  obtain ⟨l, hl⟩ := exists_safe_scale diagonal
    (fun i (l : Fin k) => Forbidden τ (geometricScale τ θ l.val) (x i))
    (by
      intro l hbad
      have hlo : 3 * τ / 8 < 0 := by simpa only [hdiag, mul_zero] using hbad.1
      linarith)
    (by
      intro i a b ha hb
      apply Fin.ext
      exact forbidden_scale_unique τ θ (x i) hτ hτone hθ (hx i) a.val b.val ha hb)
    (le_refl _)
  refine ⟨l, ?_⟩
  intro i
  rcases le_or_gt (geometricScale τ θ l.val * x i) (3 * τ / 8) with hs | hs
  · exact Or.inl hs
  · right
    by_contra hlarge
    exact hl i ⟨hs, lt_of_not_ge hlarge⟩

/-- The lower residue bracket is what makes the small classification robust. -/
theorem small_of_lower_bracket (τ G d ρ ρ' : ℝ)
    (hτ : 0 ≤ τ) (hG : 0 < G) (hρ : 0 < ρ)
    (hsmall : G * (d / ρ) ≤ 3 * τ / 8)
    (hlower : (3 / (8 * G)) * ρ ≤ ρ') : d ≤ τ * ρ' := by
  have hsmall' : G * d ≤ (3 * τ / 8) * ρ := by
    apply (div_le_iff₀ hρ).mp
    simpa only [mul_div_assoc] using hsmall
  have hden : 0 < 8 * G := by positivity
  have hlower' : 3 * ρ ≤ ρ' * (8 * G) := by
    apply (div_le_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div, mul_comm (3 : ℝ) ρ] using hlower
  have hscaled := mul_le_mul_of_nonneg_left hlower' hτ
  apply (mul_le_mul_iff_right₀ hG).mp
  nlinarith

theorem large_of_upper_bracket (G d ρ ρ' : ℝ)
    (hG : 0 < G) (hρ : 0 < ρ)
    (hlarge : 2 ≤ G * (d / ρ)) (hupper : ρ' ≤ ρ / G) : 2 * ρ' ≤ d := by
  have hlarge' : 2 * ρ ≤ G * d := by
    apply (le_div_iff₀ hρ).mp
    simpa only [mul_div_assoc] using hlarge
  have hupper' : ρ' * G ≤ ρ := (le_div_iff₀ hG).mp hupper
  apply (mul_le_mul_iff_right₀ hG).mp
  nlinarith

theorem certificate_scaled_large (τ θ d ρ : ℝ)
    (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hcertificate : θ * ρ ≤ d) (l : ℕ) :
    2 ≤ geometricScale τ θ l * (d / ρ) := by
  have hx : θ ≤ d / ρ := (le_div_iff₀ hρ).mpr hcertificate
  have hG := scale_positive τ θ hτ hθ l
  have hbase := scale_ge_base τ θ hτ hτone hθ l
  have hbase' : 2 ≤ geometricScale τ θ l * θ := (div_le_iff₀ hθ).mp hbase
  exact hbase'.trans (mul_le_mul_of_nonneg_left hx hG.le)

/-- The chosen scale is robust simultaneously for every observer and every
actual residue vector within its bracket; the original certificate stays large. -/
theorem exists_bracket_robust_scale {k : ℕ} (diagonal witness : Fin k)
    (τ θ : ℝ) (hτ : 0 < τ) (hτone : τ < 1) (hθ : 0 < θ)
    (d ρ : Fin k → ℝ) (hd : ∀ i, 0 ≤ d i) (hρ : ∀ i, 0 < ρ i)
    (hdiag : d diagonal = 0) (hcertificate : θ * ρ witness ≤ d witness) :
    ∃ l : Fin k, ∀ ρ' : Fin k → ℝ,
      (∀ i, (3 / (8 * geometricScale τ θ l.val)) * ρ i ≤ ρ' i) →
      (∀ i, ρ' i ≤ ρ i / geometricScale τ θ l.val) →
      (∀ i, d i ≤ τ * ρ' i ∨ 2 * ρ' i ≤ d i) ∧
      2 * ρ' witness ≤ d witness ∧ d diagonal ≤ τ * ρ' diagonal := by
  obtain ⟨l, hl⟩ := exists_safe_geometric_scale diagonal τ θ hτ hτone hθ
    (fun i => d i / ρ i) (fun i => div_nonneg (hd i) (hρ i).le)
    (by simp only [hdiag, zero_div])
  refine ⟨l, ?_⟩
  intro ρ' hlower hupper
  have hG := scale_positive τ θ hτ hθ l.val
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases hl i with hs | hb
    · exact Or.inl (small_of_lower_bracket τ _ _ _ _ hτ.le hG (hρ i) hs (hlower i))
    · exact Or.inr (large_of_upper_bracket _ _ _ _ hG (hρ i) hb (hupper i))
  · apply large_of_upper_bracket _ _ _ _ hG (hρ witness) _ (hupper witness)
    exact certificate_scaled_large τ θ _ _ hτ hτone hθ (hρ witness) hcertificate l.val
  · apply small_of_lower_bracket τ _ _ _ _ hτ.le hG (hρ diagonal) _ (hlower diagonal)
    simp only [hdiag, zero_div, mul_zero]
    positivity

/-- Scalar cost arithmetic only: the success probabilities and geometric waiting
time interpretations must be proved separately in the probabilistic protocol. -/
theorem numerical_attempt_envelope : (4 : ℝ) + 3 * (64 / 63) < 8 := by norm_num

/-- The crude finite stage ledger used with a k(k−1) iteration cap. -/
theorem finite_stage_iteration_bound {Stage : Type*}
    (stages : Finset Stage) (population : Stage → ℕ) (N : ℕ)
    (hstage : stages.card ≤ N) (hpopulation : ∀ s ∈ stages, population s ≤ N) :
    (∑ s ∈ stages, population s * (population s - 1)) ≤ N ^ 3 := by
  calc
    (∑ s ∈ stages, population s * (population s - 1)) ≤ ∑ _s ∈ stages, N ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have h := hpopulation s hs
      have hsub : population s - 1 ≤ N := (Nat.sub_le _ _).trans h
      simpa only [pow_two] using Nat.mul_le_mul h hsub
    _ = stages.card * N ^ 2 := by simp
    _ ≤ N * N ^ 2 := Nat.mul_le_mul_right _ hstage
    _ = N ^ 3 := by ring

#print axioms fractional_row_has_two_variables
#print axioms sparse_fractional_atom_bound
#print axioms one_sided_dummy_rounding
#print axioms dropped_row_error
#print axioms exists_safe_scale
#print axioms forbidden_scale_unique
#print axioms exists_bracket_robust_scale
#print axioms finite_stage_iteration_bound

end EnvyFreeResearch.R3Refinement
