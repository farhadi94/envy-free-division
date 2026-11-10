import EnvyFreeResearch.Full.UpperGridInterpolationExpectation

/-! Actual iid exchangeability for endpoints computed from a sorted grid.
Repeated sample coordinates are handled by sharing a charge within the fiber.
This is a reusable integration backend; the physical peeling instantiation
must still connect its bad set to the charged endpoints. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperStability
open MeasureTheory UpperSortedGrid UpperGridInterpolation
open scoped Classical BigOperators
variable {n K : ℕ}

/-- A deterministic endpoint procedure sees the sorted sample values.
Each output endpoint contributes one charge, shared equally among coinciding
sample coordinates. Distinct sample coordinates receive the ordinary count. -/
def chargeScore (protect : (Fin n → ℝ) → Fin K → ℝ) (samples : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k, if samples i = protect (sorted samples) k
    then 1 / fiberCount samples (protect (sorted samples) k) else 0

lemma chargeScore_nonneg (protect : (Fin n → ℝ) → Fin K → ℝ)
    (samples : Fin n → ℝ) (i : Fin n) : 0 ≤ chargeScore protect samples i := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact div_nonneg (by norm_num) (fiberCount_nonneg _ _)
  · exact le_rfl

lemma sum_fiberCharge (samples : Fin n → ℝ) (z : ℝ) :
    (∑ i : Fin n, if samples i = z then 1 / fiberCount samples z else 0) ≤ 1 := by
  have he : (∑ i : Fin n, if samples i = z then 1 / fiberCount samples z else 0) =
      fiberCount samples z / fiberCount samples z := by
    unfold fiberCount
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he]
  by_cases h : fiberCount samples z = 0
  · simp [h]
  · simp [h]

lemma sum_chargeScore_le (protect : (Fin n → ℝ) → Fin K → ℝ)
    (samples : Fin n → ℝ) : (∑ i, chargeScore protect samples i) ≤ K := by
  unfold chargeScore
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _k : Fin K, (1 : ℝ) := Finset.sum_le_sum (fun k _ => sum_fiberCharge samples _)
    _ = _ := by simp

lemma chargeScore_le (protect : (Fin n → ℝ) → Fin K → ℝ)
    (samples : Fin n → ℝ) (i : Fin n) : chargeScore protect samples i ≤ K :=
  (Finset.single_le_sum (fun j _ => chargeScore_nonneg protect samples j) (Finset.mem_univ i)).trans
    (sum_chargeScore_le protect samples)

lemma fiberCount_perm (samples : Fin n → ℝ) (e : Equiv.Perm (Fin n)) (z : ℝ) :
    fiberCount (samples ∘ e) z = fiberCount samples z := by
  unfold fiberCount
  exact Equiv.sum_comp e (fun i => if samples i = z then 1 else 0)

lemma chargeScore_swap (protect : (Fin n → ℝ) → Fin K → ℝ)
    (samples : Fin n → ℝ) (i j : Fin n) :
    chargeScore protect (samples ∘ Equiv.swap i j) i = chargeScore protect samples j := by
  unfold chargeScore
  rw [sorted_perm]
  simp only [Function.comp_apply,Equiv.swap_apply_left]
  simp_rw [fiberCount_perm]

lemma chargeScore_measurable (protect : (Fin n → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => protect s k)) (i : Fin n) :
    Measurable (fun samples => chargeScore protect samples i) := by
  have hs : Measurable (sorted (m := n)) := sorted_measurable id (fun j => measurable_pi_apply j)
  apply Finset.measurable_sum
  intro k _
  have he := (hp k).comp hs
  have hc : Measurable (fun s : Fin n → ℝ => fiberCount s (protect (sorted s) k)) := by
    apply Finset.measurable_sum
    intro j _
    exact measurable_const.ite (measurableSet_eq_fun (measurable_pi_apply j) he) measurable_const
  exact (measurable_const.div hc).ite
    (measurableSet_eq_fun (measurable_pi_apply i) he) measurable_const

lemma chargeScore_integrable (protect : (Fin n → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => protect s k)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : Fin n) : Integrable (fun samples => chargeScore protect samples i)
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply Integrable.mono' (integrable_const (K : ℝ)) (chargeScore_measurable protect hp i).aestronglyMeasurable
  exact ae_of_all _ (fun samples => by
    rw [Real.norm_eq_abs,abs_of_nonneg (chargeScore_nonneg protect samples i)]
    exact chargeScore_le protect samples i)

lemma chargeScore_integral_eq (protect : (Fin n → ℝ) → Fin K → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (i j : Fin n) :
    (∫ samples, chargeScore protect samples i ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ samples, chargeScore protect samples j ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.swap i j)
  have he (samples : Fin n → ℝ) : e samples = samples ∘ Equiv.swap i j := by
    funext k
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ)
      (Equiv.swap i j) samples (Equiv.swap i j k)
    simpa [e] using h
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) (Equiv.swap i j)
  calc
    _ = ∫ samples, chargeScore protect (e samples) i ∂Measure.pi (fun _ : Fin n => μ) :=
      (hp.integral_comp' (fun samples => chargeScore protect samples i)).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun samples => by
      change chargeScore protect (e samples) i = _
      rw [he,chargeScore_swap]))

/-- The factor `1/n` is derived from the actual iid product law and the
sort-based implementation, rather than assumed exchangeability of scores. -/
theorem chargeScore_expectation_le (protect : (Fin n → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => protect s k)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : Fin n) :
    (∫ samples, chargeScore protect samples i ∂Measure.pi (fun _ : Fin n => μ)) ≤ (K : ℝ)/n := by
  have hint (j : Fin n) := chargeScore_integrable protect hp μ j
  have hsum : (∑ j : Fin n, ∫ samples, chargeScore protect samples j
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ K := calc
    _ = ∫ samples, ∑ j : Fin n, chargeScore protect samples j
        ∂Measure.pi (fun _ : Fin n => μ) := (integral_finsetSum _ (fun j _ => hint j)).symm
    _ ≤ ∫ _samples : Fin n → ℝ, (K : ℝ) ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono (integrable_finsetSum _ (fun j _ => hint j)) (integrable_const _)
        (sum_chargeScore_le protect)
    _ = _ := by simp
  have heq (j : Fin n) := chargeScore_integral_eq protect μ j i
  simp_rw [heq] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  exact (le_div_iff₀ hn).mpr (by nlinarith)

/-- Independent test-point formulation, by disintegration of the actual
product measure; intended endpoint budget is `K=4*slots+4*rowPairs`. -/
theorem integrated_charge_le {m : ℕ}
    (protect : (Fin (m+1) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => protect s k)) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ samples : Fin m → ℝ, ∫ test,
      chargeScore protect (Fin.cons test samples) 0 ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ (K : ℝ)/(m+1 : ℕ) := by
  let score := fun samples : Fin (m+1) → ℝ => chargeScore protect samples 0
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm
  have he (z : ℝ × (Fin m → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have hint : Integrable (score ∘ e) (μ.prod (Measure.pi (fun _ : Fin m => μ))) :=
    hpres.integrable_comp_of_integrable (chargeScore_integrable protect hp μ 0)
  have heq : (∫ samples : Fin m → ℝ, ∫ test,
      chargeScore protect (Fin.cons test samples) 0 ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) =
      ∫ samples, score samples ∂Measure.pi (fun _ : Fin (m+1) => μ) := by
    calc
      _ = ∫ z : ℝ × (Fin m → ℝ), score (e z) ∂μ.prod (Measure.pi (fun _ : Fin m => μ)) := by
        simpa only [Function.comp_def,he,score] using (integral_prod_symm (score ∘ e) hint).symm
      _ = _ := hpres.integral_comp' score
  rw [heq]
  exact chargeScore_expectation_le protect hp μ 0

end EnvyFreeResearch.Full.RefinedUpperStability
