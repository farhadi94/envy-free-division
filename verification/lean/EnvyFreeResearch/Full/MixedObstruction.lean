import EnvyFreeResearch.Full.MixedDensity
import EnvyFreeResearch.CoordinatedFamily

/-! The tail obstruction for actual signed measures and physical measurable
shares. No fractional-cell encoding is assumed. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedObstruction
open Set MeasureTheory MixedDensity CoordinatedFamily

abbrev domainMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

def value (R : Row) (A : Set ℝ) : ℝ := ∫ x in A, R.density x ∂domainMeasure

@[simp] theorem value_univ (R : Row) : value R univ = R.cumulative 1 := by
  simp only [value, setIntegral_univ, Row.cumulative,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem value_signedMeasure (R : Row) (A : Set ℝ) (hA : MeasurableSet A) :
    value R A = R.signedMeasure (A ∩ Ioc (0 : ℝ) 1) := by
  rw [R.signedMeasure_apply _ (hA.inter measurableSet_Ioc)]
  unfold value domainMeasure
  rw [Measure.restrict_restrict hA]

@[simp] theorem value_complement (R : Row) (C : Set ℝ) (hC : MeasurableSet C) :
    value R C + value R Cᶜ = R.cumulative 1 := by
  have h := integral_add_compl hC (R.integrable.restrict (s := Ioc (0 : ℝ) 1))
  simpa only [value, Row.cumulative,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

def transferDensity (α : ℝ) (f g : ℝ → ℝ) (A B C : Set ℝ) (x : ℝ) : ℝ :=
  α * ((Cᶜ.indicator f) x + (Cᶜ.indicator g) x) +
    (A.indicator f) x + (B.indicator g) x

theorem transferDensity_nonpositive {α : ℝ} {f g : ℝ → ℝ} {A B C : Set ℝ}
    (hα : 0 ≤ α) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (x : ℝ) (hcoeff : PairCoefficients α (f x) (g x)) :
    transferDensity α f g A B C x ≤ 0 := by
  classical
  by_cases hxC : x ∈ C
  · have hxA : x ∉ A := fun hx => Set.disjoint_left.mp hAC hx hxC
    have hxB : x ∉ B := fun hx => Set.disjoint_left.mp hBC hx hxC
    simp [transferDensity, hxC, hxA, hxB]
  · by_cases hxA : x ∈ A
    · have hxB : x ∉ B := fun hx => Set.disjoint_left.mp hAB hxA hx
      simp only [transferDensity, mem_compl_iff, hxC, not_false_eq_true,
        indicator_of_mem, hxA, indicator_of_notMem hxB, add_zero]
      linarith [hcoeff.1]
    · by_cases hxB : x ∈ B
      · simp [transferDensity, hxC, hxA, hxB]
        linarith [hcoeff.2.1]
      · simp only [transferDensity, mem_compl_iff, hxC, not_false_eq_true,
          indicator_of_mem, indicator_of_notMem hxA, indicator_of_notMem hxB, add_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hα hcoeff.2.2

theorem transferDensity_on_owner {α : ℝ} {f g : ℝ → ℝ} {A B C : Set ℝ}
    (hAC : Disjoint A C) (hBC : Disjoint B C) {x : ℝ} (hxC : x ∈ C) :
    transferDensity α f g A B C x = 0 := by
  have hxA : x ∉ A := fun hx => Set.disjoint_left.mp hAC hx hxC
  have hxB : x ∉ B := fun hx => Set.disjoint_left.mp hBC hx hxC
  simp [transferDensity, hxC, hxA, hxB]

/-- Integrating a nonpositive transfer density gives the physical envy
certificate. This form also permits endpoint-null reflection arguments. -/
theorem physical_envy_sum_of_nonpositive (R S : Row) (α : ℝ) (A B C : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hR : R.cumulative 1 = 1) (hS : S.cumulative 1 = 1)
    (hpoint : ∀ᵐ x ∂domainMeasure, transferDensity α R.density S.density A B C x ≤ 0) :
    2 * α ≤ (α * value R C - value R A) + (α * value S C - value S B) := by
  have hiR : Integrable R.density domainMeasure := R.integrable.restrict
  have hiS : Integrable S.density domainMeasure := S.integrable.restrict
  have hiRc := hiR.indicator hC.compl
  have hiSc := hiS.indicator hC.compl
  have hiRa := hiR.indicator hA
  have hiSb := hiS.indicator hB
  have hint := integral_nonpos_of_ae hpoint
  have heq : (∫ x, transferDensity α R.density S.density A B C x ∂domainMeasure) =
      α * (value R Cᶜ + value S Cᶜ) + value R A + value S B := by
    have hout := integral_add ((hiRc.add hiSc).const_mul α |>.add hiRa) hiSb
    have hmid := integral_add ((hiRc.add hiSc).const_mul α) hiRa
    have hin := integral_add hiRc hiSc
    simp only [Pi.add_apply] at hout hmid hin
    unfold transferDensity
    rw [hout, hmid, integral_const_mul, hin]
    simp only [integral_indicator hC.compl, integral_indicator hA, integral_indicator hB, value]
  rw [heq] at hint
  have hcR := value_complement R C hC
  have hcS := value_complement S C hC
  rw [hR] at hcR
  rw [hS] at hcS
  have hRc : value R Cᶜ = 1 - value R C := by linarith
  have hSc : value S Cᶜ = 1 - value S C := by linarith
  rw [hRc, hSc] at hint
  nlinarith

/-- Two nonowners of an uncut final tail have total signed envy at least 2α.
The shares may be arbitrary measurable sets; only disjointness is needed. -/
theorem physical_envy_sum (R S : Row) (α l : ℝ) (A B C : Set ℝ)
    (hα : 0 ≤ α) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hR : R.cumulative 1 = 1) (hS : S.cumulative 1 = 1)
    (hcoeff : ∀ x ∈ Ioc (0 : ℝ) l,
      PairCoefficients α (R.density x) (S.density x))
    (htail : Ioc l (1 : ℝ) ⊆ C) :
    2 * α ≤ (α * value R C - value R A) + (α * value S C - value S B) := by
  have hiR : Integrable R.density domainMeasure := R.integrable.restrict
  have hiS : Integrable S.density domainMeasure := S.integrable.restrict
  have hiRc := hiR.indicator hC.compl
  have hiSc := hiS.indicator hC.compl
  have hiRa := hiR.indicator hA
  have hiSb := hiS.indicator hB
  have hpoint : ∀ᵐ x ∂domainMeasure,
      transferDensity α R.density S.density A B C x ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    by_cases hxl : x ≤ l
    · exact transferDensity_nonpositive hα hAB hAC hBC x (hcoeff x ⟨hx.1, hxl⟩)
    · rw [transferDensity_on_owner hAC hBC (htail ⟨lt_of_not_ge hxl, hx.2⟩)]
  have hint := integral_nonpos_of_ae hpoint
  have heq : (∫ x, transferDensity α R.density S.density A B C x ∂domainMeasure) =
      α * (value R Cᶜ + value S Cᶜ) + value R A + value S B := by
    have hout := integral_add ((hiRc.add hiSc).const_mul α |>.add hiRa) hiSb
    have hmid := integral_add ((hiRc.add hiSc).const_mul α) hiRa
    have hin := integral_add hiRc hiSc
    simp only [Pi.add_apply] at hout hmid hin
    unfold transferDensity
    rw [hout, hmid, integral_const_mul, hin]
    simp only [integral_indicator hC.compl, integral_indicator hA, integral_indicator hB, value]
  rw [heq] at hint
  have hcR := value_complement R C hC
  have hcS := value_complement S C hC
  rw [hR] at hcR
  rw [hS] at hcS
  nlinarith

/-- At least one actual signed envy inequality fails at every ε < α. -/
theorem physical_violation (R S : Row) (α ε l : ℝ) (A B C : Set ℝ)
    (hα : 0 ≤ α) (hε : ε < α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hR : R.cumulative 1 = 1) (hS : S.cumulative 1 = 1)
    (hcoeff : ∀ x ∈ Ioc (0 : ℝ) l,
      PairCoefficients α (R.density x) (S.density x))
    (htail : Ioc l (1 : ℝ) ⊆ C) :
    ε < α * value R C - value R A ∨ ε < α * value S C - value S B := by
  have h := physical_envy_sum R S α l A B C hα hA hB hC hAB hAC hBC hR hS hcoeff htail
  by_contra hn
  push Not at hn
  linarith

end EnvyFreeResearch.Full.MixedObstruction
