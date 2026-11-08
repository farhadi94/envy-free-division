import EnvyFreeResearch.Full.UpperGridInterpolationMeasurable
import Mathlib.MeasureTheory.Integral.Pi

/-! An explicit augmented grid and its symmetric sample-deletion scores. -/

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

variable {Row : Type*} [Fintype Row] [Nonempty Row] {b n : ℕ}

/-- Only the permanent logical boundaries and the new sample coordinates
are sorted. Old physical component joins are not added here. -/
def augmented (permanent : Fin b → ℝ) (samples : Fin n → ℝ) : Fin (b + n + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc (Fin.addCases permanent samples) 1)

def sampleLabel (i : Fin n) : Fin (b + n + 2) := (Fin.natAdd b i).castSucc.succ

theorem sampleLabel_injective : Function.Injective (sampleLabel (b := b) (n := n)) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [sampleLabel, Fin.val_succ, Fin.val_castSucc, Fin.val_natAdd] at this
  omega

@[simp] theorem augmented_sample (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) :
    augmented permanent samples (sampleLabel i) = samples i := by
  simp only [augmented, sampleLabel, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_right]

private theorem sampleLabel_ne_zero (i : Fin n) : sampleLabel (b := b) i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [sampleLabel] at this

private theorem sampleLabel_ne_last (i : Fin n) :
    sampleLabel (b := b) i ≠ Fin.last (b + n + 1) := by
  intro h
  have := congrArg Fin.val h
  simp [sampleLabel] at this
  omega

private theorem sampleLabel_ne_permanent (i : Fin n) (j : Fin b) :
    sampleLabel (b := b) i ≠ (Fin.castAdd n j).castSucc.succ := by
  intro h
  have := congrArg Fin.val h
  simp [sampleLabel] at this
  omega

/-- Swapping two sample labels induces the literal corresponding swap of
the raw augmented tuple while fixing all permanent and outer boundaries. -/
theorem augmented_swap (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i j : Fin n) :
    augmented permanent (samples ∘ Equiv.swap i j) =
      augmented permanent samples ∘ Equiv.swap (sampleLabel i) (sampleLabel j) := by
  funext k
  refine Fin.cases ?_ (fun q => ?_) k
  · simp [Equiv.swap_apply_def, sampleLabel_ne_zero, Ne.symm (sampleLabel_ne_zero i),
      Ne.symm (sampleLabel_ne_zero j), augmented]
  · refine Fin.lastCases ?_ (fun q => ?_) q
    · simp [Equiv.swap_apply_def, sampleLabel_ne_last, Ne.symm (sampleLabel_ne_last i),
        Ne.symm (sampleLabel_ne_last j), augmented]
    · refine Fin.addCases ?_ ?_ q
      · intro p
        simp [Equiv.swap_apply_def, sampleLabel_ne_permanent,
          Ne.symm (sampleLabel_ne_permanent i p), Ne.symm (sampleLabel_ne_permanent j p), augmented]
      · intro p
        change augmented permanent (samples ∘ Equiv.swap i j) (sampleLabel p) =
          augmented permanent samples (Equiv.swap (sampleLabel i) (sampleLabel j) (sampleLabel p))
        simp only [augmented_sample, Function.comp_apply, Equiv.swap_apply_def]
        by_cases hi : p = i
        · subst p; simp
        · by_cases hj : p = j
          · subst p
            simp [hi, sampleLabel_injective.ne hi]
          · simp [hi, hj, sampleLabel_injective.ne hi, sampleLabel_injective.ne hj]

def sampleScore (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (permanent : Fin b → ℝ)
    (samples : Fin n → ℝ) (i : Fin n) : ℝ :=
  gridScore F L (augmented permanent samples) (samples i)

theorem sampleScore_nonneg (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (permanent : Fin b → ℝ)
    (samples : Fin n → ℝ) (i : Fin n) : 0 ≤ sampleScore F L permanent samples i :=
  gridScore_nonneg _ _ _ _

theorem sampleScore_swap (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (permanent : Fin b → ℝ)
    (samples : Fin n → ℝ) (i j : Fin n) :
    sampleScore F L permanent (samples ∘ Equiv.swap i j) i = sampleScore F L permanent samples j := by
  simp only [sampleScore, augmented_swap, gridScore_perm, Function.comp_apply, Equiv.swap_apply_left]

theorem sum_sampleScore (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (hL : Monotone L)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) :
    ∑ i, sampleScore F L permanent samples i ≤ 2 * ((Fintype.card Row : ℝ) - 1) := by
  have h := sum_selected_gridScore F L hL (augmented permanent samples)
    (sampleLabel (b := b)) sampleLabel_injective
  simpa only [augmented_sample, sampleScore] using h

theorem sampleScore_le_bound (F : Row → ℝ → ℝ) (L : ℝ → ℝ) (hL : Monotone L)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) :
    sampleScore F L permanent samples i ≤ 2 * ((Fintype.card Row : ℝ) - 1) :=
  (Finset.single_le_sum (f := fun j => sampleScore F L permanent samples j)
    (fun _ _ => sampleScore_nonneg _ _ _ _ _) (Finset.mem_univ i)).trans
      (sum_sampleScore F L hL permanent samples)

theorem augmented_measurable (permanent : Fin b → ℝ) (e : Fin (b + n + 2)) :
    Measurable (fun samples : Fin n → ℝ => augmented permanent samples e) := by
  refine Fin.cases ?_ (fun j => ?_) e
  · exact measurable_const
  · refine Fin.lastCases ?_ (fun q => ?_) j
    · simp only [augmented, Fin.cons_succ, Fin.snoc_last]
      exact measurable_const
    · refine Fin.addCases (fun p => ?_) (fun i => ?_) q
      · simp only [augmented, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_left]
        exact measurable_const
      · simp only [augmented, Fin.cons_succ, Fin.snoc_castSucc, Fin.addCases_right]
        exact measurable_pi_apply i

theorem sampleScore_measurable (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Measurable L) (permanent : Fin b → ℝ) (i : Fin n) :
    Measurable (fun samples => sampleScore F L permanent samples i) :=
  gridScore_measurable F hF L hL (augmented permanent) (augmented_measurable permanent)
    _ (measurable_pi_apply i)

theorem sampleScore_integrable (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Monotone L) (hLm : Measurable L) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin n) :
    Integrable (fun samples => sampleScore F L permanent samples i) (Measure.pi (fun _ : Fin n => μ)) := by
  apply (integrable_const (2 * ((Fintype.card Row : ℝ) - 1))).mono'
    (sampleScore_measurable F hF L hLm permanent i).aestronglyMeasurable
  exact ae_of_all _ (fun samples => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sampleScore_nonneg F L permanent samples i)]
    exact sampleScore_le_bound F L hL permanent samples i)

end EnvyFreeResearch.Full.UpperGridInterpolation
