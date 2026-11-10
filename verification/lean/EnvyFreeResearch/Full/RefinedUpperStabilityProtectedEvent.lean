import EnvyFreeResearch.Full.RefinedUpperStabilityAugmented
import EnvyFreeResearch.Full.RefinedUpperStabilityProcedure

/-! A complete iid compression bound for the actual protected endpoints. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperStability
open MeasureTheory Set UpperSortedGrid UpperGridInterpolation RefinedUpperPeeling
open scoped Classical BigOperators
variable {b n K : ℕ}

def coincidence (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) : ℝ :=
  if ∃ k, procedure (sorted (augmented permanent samples)) k = samples i then 1 else 0

lemma coincidence_nonneg (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) :
    0 ≤ coincidence procedure permanent samples i := by unfold coincidence; split_ifs <;> norm_num

lemma coincidence_le_one (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n) :
    coincidence procedure permanent samples i ≤ 1 := by unfold coincidence; split_ifs <;> norm_num

lemma coincidence_measurable (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k)) (permanent : Fin b → ℝ) (i : Fin n) :
    Measurable (fun samples => coincidence procedure permanent samples i) := by
  apply measurable_const.ite _ measurable_const
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_eq_fun
    ((hp k).comp (sorted_measurable (augmented permanent) (augmented_measurable permanent)))
    (measurable_pi_apply i)

lemma augmentedChargeScore_measurable (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k)) (permanent : Fin b → ℝ) (i : Fin n) :
    Measurable (fun samples => augmentedChargeScore procedure permanent samples i) := by
  simp_rw [augmentedChargeScore_eq]
  apply chargeScore_measurable
  intro k
  exact (hp k).comp (sorted_measurable (augmented permanent) (augmented_measurable permanent))

lemma coincidence_le_charge_unique (procedure : (Fin (b+n+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin n → ℝ) (i : Fin n)
    (hunique : ∀ j, samples j = samples i → j = i) :
    coincidence procedure permanent samples i ≤ augmentedChargeScore procedure permanent samples i := by
  have hn := chargeScore_nonneg (fun s => procedure (sorted (augmented permanent s))) samples i
  rw [← augmentedChargeScore_eq] at hn
  unfold coincidence
  split_ifs with he
  · obtain ⟨k,hk⟩ := he
    have hcount : fiberCount samples (procedure (sorted (augmented permanent samples)) k) = 1 := by
      rw [hk]
      have hiff (j : Fin n) : samples j = samples i ↔ j = i := ⟨hunique j,fun h => h ▸ rfl⟩
      simp [fiberCount,hiff]
    have hsum := Finset.single_le_sum (s := (Finset.univ : Finset (Fin K)))
      (f := fun l => if samples i = procedure (sorted (augmented permanent samples)) l
        then 1/fiberCount samples (procedure (sorted (augmented permanent samples)) l) else 0)
      (fun l _ => by split_ifs; exact div_nonneg (by norm_num) (fiberCount_nonneg _ _); exact le_rfl)
      (Finset.mem_univ k)
    have hcount' : fiberCount samples (samples i) = 1 := by simpa only [hk] using hcount
    simpa [augmentedChargeScore,hk,hcount'] using hsum
  · exact hn

lemma integrable_bounded_nonneg {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) : Integrable f ν := by
  apply Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact hB x)

/-- The expected probability that the independent test equals one of the
procedure's protected endpoints is at most the number of slots divided by
`m+1`. This is proved for the actual procedure, i.i.d. law and Borel event. -/
theorem integrated_coincidence_le {m : ℕ}
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (∫ samples : Fin m → ℝ, ∫ test, coincidence procedure permanent (Fin.cons test samples) 0 ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ (K : ℝ)/(m+1 : ℕ) := by
  let ν := Measure.pi (fun _ : Fin m => μ)
  let join (z : (Fin m → ℝ) × ℝ) : Fin (m+1) → ℝ := Fin.cons z.2 z.1
  have hj : Measurable join := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases measurable_snd (fun j => (measurable_pi_apply j).comp measurable_fst) i
  let event := fun z : (Fin m → ℝ) × ℝ => coincidence procedure permanent (join z) 0
  let charge := fun z : (Fin m → ℝ) × ℝ => augmentedChargeScore procedure permanent (join z) 0
  have heM : Measurable event := (coincidence_measurable procedure hp permanent 0).comp hj
  have hcM : Measurable charge := (augmentedChargeScore_measurable procedure hp permanent 0).comp hj
  have he0 (z) : 0 ≤ event z := coincidence_nonneg _ _ _ _
  have he1 (z) : event z ≤ 1 := coincidence_le_one _ _ _ _
  have hc0 (z) : 0 ≤ charge z := by
    change 0 ≤ augmentedChargeScore procedure permanent (join z) 0
    rw [augmentedChargeScore_eq]
    exact chargeScore_nonneg _ _ _
  have hcK (z) : charge z ≤ K := by
    change augmentedChargeScore procedure permanent (join z) 0 ≤ K
    rw [augmentedChargeScore_eq]
    exact chargeScore_le _ _ _
  have heI := integrable_bounded_nonneg (ν.prod μ) event heM 1 he0 he1
  have hcI := integrable_bounded_nonneg (ν.prod μ) charge hcM K hc0 hcK
  have hinner (samples : Fin m → ℝ) :
      (∫ test, event (samples,test) ∂μ) ≤ ∫ test, charge (samples,test) ∂μ := by
    have heInt := integrable_bounded_nonneg μ (fun test => event (samples,test))
      (heM.comp (measurable_const.prodMk measurable_id)) 1 (fun t => he0 _) (fun t => he1 _)
    have hcInt := integrable_bounded_nonneg μ (fun test => charge (samples,test))
      (hcM.comp (measurable_const.prodMk measurable_id)) K (fun t => hc0 _) (fun t => hcK _)
    apply integral_mono_ae heInt hcInt
    have hfresh : ∀ᵐ test ∂μ, ∀ j, test ≠ samples j := ae_all_iff.mpr (fun j => μ.ae_ne (samples j))
    filter_upwards [hfresh] with test htest
    apply coincidence_le_charge_unique
    intro j
    refine Fin.cases (by simp) (fun j hj => ?_) j
    exact False.elim (htest j (by simpa [join] using hj.symm))
  calc
    _ ≤ ∫ samples : Fin m → ℝ, ∫ test,
        augmentedChargeScore procedure permanent (Fin.cons test samples) 0 ∂μ ∂ν :=
      integral_mono heI.integral_prod_left hcI.integral_prod_left hinner
    _ ≤ _ := integrated_augmented_charge_le procedure hp permanent μ

/-- Specialization to the concrete maximum-determinant peeling and final
witness procedure, with exactly `4*slots+4*rowPairs` protected endpoint slots. -/
theorem integrated_actual_endpoint_event_le {Row : Type*} {a m : ℕ}
    (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r)) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (∫ samples : Fin m → ℝ, ∫ test,
      coincidence (endpointProcedure F coarse jobs finalJobs) permanent (Fin.cons test samples) 0 ∂μ
      ∂Measure.pi (fun _ : Fin m => μ)) ≤
      ((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ) := by
  simpa only [Nat.mul_add] using integrated_coincidence_le
    (endpointProcedure F coarse jobs finalJobs) (endpointProcedure_measurable F hF coarse jobs finalJobs)
    permanent μ

/-- An explicit analytical bad set: insert the test point, run the actual
procedure, and test whether its coordinate is one of the protected endpoints.
Its complement has the pointwise stability property; minimality is unnecessary. -/
def protectedBad {m : ℕ}
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) : Set ℝ :=
  {test | ∃ k, procedure (sorted (augmented permanent (Fin.cons test samples))) k = test}

lemma protectedBad_measurable {m : ℕ}
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k))
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) :
    MeasurableSet (protectedBad procedure permanent samples) := by
  have hj : Measurable (fun test : ℝ => (Fin.cons test samples : Fin (m+1) → ℝ)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases measurable_id (fun _ => measurable_const) i
  simp only [protectedBad,ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_eq_fun (((hp k).comp
    (sorted_measurable (augmented permanent) (augmented_measurable permanent))).comp hj) measurable_id

lemma coincidence_integral_eq_measure {m : ℕ}
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k))
    (permanent : Fin b → ℝ) (samples : Fin m → ℝ) (μ : Measure ℝ) :
    (∫ test, coincidence procedure permanent (Fin.cons test samples) 0 ∂μ) =
      μ.real (protectedBad procedure permanent samples) := by
  calc
    _ = ∫ test, (protectedBad procedure permanent samples).indicator (fun _ => (1 : ℝ)) test ∂μ := by
      apply integral_congr_ae
      filter_upwards with test
      by_cases h : test ∈ protectedBad procedure permanent samples
      · rw [Set.indicator_of_mem h]
        exact if_pos h
      · rw [Set.indicator_of_notMem h]
        exact if_neg h
    _ = _ := integral_indicator_one (protectedBad_measurable procedure hp permanent samples)

/-- Complete expectation bound for the explicit Borel analytical bad set,
instantiated with the actual maximum-determinant endpoint procedure. -/
theorem expected_protectedBad_measure_le {Row : Type*} {a m : ℕ}
    (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r)) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (∫ samples : Fin m → ℝ,
      μ.real (protectedBad (endpointProcedure F coarse jobs finalJobs) permanent samples)
      ∂Measure.pi (fun _ : Fin m => μ)) ≤
      ((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ) := by
  have h := integrated_actual_endpoint_event_le (m := m) F hF coarse jobs finalJobs permanent μ
  simp_rw [coincidence_integral_eq_measure _ (endpointProcedure_measurable F hF coarse jobs finalJobs)] at h
  exact h

end EnvyFreeResearch.Full.RefinedUpperStability
