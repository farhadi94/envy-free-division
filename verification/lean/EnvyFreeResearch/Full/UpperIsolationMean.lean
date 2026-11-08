import EnvyFreeResearch.Full.UpperSeedProbability

/-! The logarithmic truncated expectation is obtained by integrating the
proved seed-threshold tail bound. No expected-value hypothesis is supplied. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace EnvyFreeResearch.Full.UpperIsolationMean

open UpperSeeds UpperSeedProbability

variable {L : ℕ}

theorem truncated_charge_expectation (gamma : Fin L → ℝ) (A lam offset a : ℝ)
    (hA : 0 < A) (hlam : 0 ≤ lam) (ha : 0 < a) (haone : a ≤ 1)
    (hgap : ∀ i, A / 3 ≤ |gamma i|) :
    (∫ t, max (charge A lam (offset + value gamma t) - a) 0 ∂thresholdLaw) ≤
      (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) := by
  let Z : Fin (L + 1) → ℝ := fun t => max (charge A lam (offset + value gamma t) - a) 0
  have hM : 0 ≤ 1 - a := by linarith
  have hZint : Integrable Z thresholdLaw := Integrable.of_finite
  have hZnonneg : 0 ≤ᵐ[thresholdLaw] Z := ae_of_all _ (fun _ => le_max_right _ _)
  have hZbounded : Z ≤ᵐ[thresholdLaw] (fun _ => 1 - a) := by
    apply ae_of_all
    intro t
    exact max_le (sub_le_sub_right (charge_le_one A lam _) a) hM
  have htail : Antitone (fun v : ℝ => thresholdLaw.real {t | v ≤ Z t}) := by
    intro u v huv
    exact measureReal_mono (fun _ ht => huv.trans ht)
  have htailint : IntervalIntegrable (fun v : ℝ => thresholdLaw.real {t | v ≤ Z t})
      volume 0 (1 - a) := htail.intervalIntegrable
  have hinv : ContinuousOn (fun v : ℝ => (v + a)⁻¹) (Icc 0 (1 - a)) := by
    apply (continuousOn_id.add continuousOn_const).inv₀
    intro v hv
    exact ne_of_gt (by linarith [hv.1] : 0 < v + a)
  have hinvint : IntervalIntegrable (fun v : ℝ => (v + a)⁻¹) volume 0 (1 - a) :=
    hinv.intervalIntegrable_of_Icc hM
  have hmainint : IntervalIntegrable (fun v : ℝ => 12 * lam / (v + a)) volume 0 (1 - a) := by
    simpa only [div_eq_mul_inv] using hinvint.const_mul (12 * lam)
  have hboundint : IntervalIntegrable
      (fun v : ℝ => (12 * lam / (v + a) + 1) / (L + 1 : ℕ)) volume 0 (1 - a) :=
    (hmainint.add intervalIntegrable_const).div_const _
  have hlogintegral : (∫ v : ℝ in 0..1 - a, (v + a)⁻¹) = Real.log (1 / a) := by
    rw [intervalIntegral.integral_comp_add_right (fun v : ℝ => v⁻¹) a,
      zero_add, sub_add_cancel, integral_inv_of_pos ha (by norm_num)]
  have hmainintegral : (∫ v : ℝ in 0..1 - a, 12 * lam / (v + a)) =
      12 * lam * Real.log (1 / a) := by
    change (∫ v : ℝ in 0..1 - a, (12 * lam) * (v + a)⁻¹) = _
    rw [intervalIntegral.integral_const_mul, hlogintegral]
  change (∫ t, Z t ∂thresholdLaw) ≤ _
  calc
    (∫ t, Z t ∂thresholdLaw) =
        ∫ v : ℝ in 0..1 - a, thresholdLaw.real {t | v ≤ Z t} := by
      rw [hZint.integral_eq_integral_Ioc_meas_le hZnonneg hZbounded,
        intervalIntegral.integral_of_le hM]
    _ ≤ ∫ v : ℝ in 0..1 - a, (12 * lam / (v + a) + 1) / (L + 1 : ℕ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hM htailint hboundint
      intro v hv
      have hu : 0 < v + a := by linarith [hv.1]
      have huone : v + a ≤ 1 := by linarith [hv.2]
      have heq : {t | v ≤ Z t} = {t | v + a ≤ charge A lam (offset + value gamma t)} := by
        ext t
        change v ≤ max (charge A lam (offset + value gamma t) - a) 0 ↔
          v + a ≤ charge A lam (offset + value gamma t)
        rw [le_max_iff]
        constructor
        · rintro (h | h) <;> linarith [hv.1]
        · intro h
          exact Or.inl (by linarith)
      rw [heq]
      have hprob := charge_tail_probability gamma A lam (v + a) offset hA hlam hu huone hgap
      have hreal := ENNReal.toReal_mono (by finiteness) hprob
      have hnonneg : 0 ≤ (12 * lam / (v + a) + 1) / (L + 1 : ℕ) := by positivity
      simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using hreal
    _ = (12 * lam * Real.log (1 / a) + 1 - a) / (L + 1 : ℕ) := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hmainint intervalIntegrable_const,
        hmainintegral, intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one, sub_zero]
      ring

end EnvyFreeResearch.Full.UpperIsolationMean
