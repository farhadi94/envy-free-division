import EnvyFreeResearch.Full.RefinedUpperStabilityExchangeability
import Mathlib.GroupTheory.Perm.Sign

/-! Iid endpoint charging for a sorted coarse-plus-sample grid. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperStability
open MeasureTheory UpperSortedGrid UpperGridInterpolation
open scoped Classical BigOperators

lemma sorted_augmented_perm {b n : ℕ} (permanent : Fin b → ℝ) (samples : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    sorted (augmented permanent (samples ∘ e)) = sorted (augmented permanent samples) := by
  induction e using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap e i j hne ih =>
    change sorted (augmented permanent ((samples ∘ e) ∘ Equiv.swap i j)) = _
    rw [augmented_swap,sorted_perm,ih]

lemma sorted_augmented_sorted {b n : ℕ} (permanent : Fin b → ℝ) (samples : Fin n → ℝ) :
    sorted (augmented permanent (sorted samples)) = sorted (augmented permanent samples) :=
  sorted_augmented_perm permanent samples (UpperSortedGrid.select samples)

/-- The measurable procedure is applied to the actual coarse-plus-sample
sorted grid; no covariance property of the procedure is assumed. -/
def augmentedChargeScore {b n K : ℕ}
    (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k, if samples i = procedure (sorted (augmented permanent samples)) k
    then 1 / fiberCount samples (procedure (sorted (augmented permanent samples)) k) else 0

lemma augmentedChargeScore_eq {b n K : ℕ}
    (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) :
    augmentedChargeScore procedure permanent samples i =
      chargeScore (fun s => procedure (sorted (augmented permanent s))) samples i := by
  simp only [augmentedChargeScore,chargeScore,sorted_augmented_sorted]

theorem integrated_augmented_charge_le {b m K : ℕ}
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k))
    (permanent : Fin b → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ samples : Fin m → ℝ, ∫ test,
      augmentedChargeScore procedure permanent (Fin.cons test samples) 0 ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ (K : ℝ)/(m+1 : ℕ) := by
  simp_rw [augmentedChargeScore_eq]
  apply integrated_charge_le
  intro k
  exact (hp k).comp (sorted_measurable (augmented permanent) (augmented_measurable permanent))

end EnvyFreeResearch.Full.RefinedUpperStability
