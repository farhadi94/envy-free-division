import EnvyFreeResearch.Full.UpperPreparedEnvelopeFamily
import EnvyFreeResearch.Full.UpperCorrectionFailure

/-! The actual prepared correction program has the combined rejection
bound on its original full preparation-history × fresh-circle product law.
The fixed reserve and original sampling buffer remain distinct. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperPreparedCorrectionProbability

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperEnvelope UpperCircularStage UpperStageMeasurable
  UpperPreparedEnvelopeMean UpperPreparedEnvelopeFamily UpperAggregateInterpolation
  UpperGridInterpolation UpperSortedGrid UpperRawPayments

variable {n k permanentCount sampleCount : ℕ} [Nonempty (Fin k)]
  {X : Type*} [MeasurableSpace X]

theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (samplingBuffer errorDomain : List Component)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain samplingBuffer))
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (hmixture : sampleLaw = UpperMixtureSampling.mixture μ active samplingBuffer)
    (parameterLaw : Measure X) [IsProbabilityMeasure parameterLaw]
    (samples : X → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (reserve : X → State n) (hreserve : Measurable reserve)
    (hdomain : ∀ x, domain (reserve x).cells = domain errorDomain)
    (cuts : X → Fin (permanentCount + sampleCount + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hgrid : ∀ x, cuts x = sorted (augmented permanent (samples x)))
    (t : X → Fin k → ℝ) (ht : ∀ j, Measurable (fun x => t x j))
    (approved : X → Bool) (happroved : Measurable approved)
    (eta lam N q b : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N) (hq : 0 < q) (hb : 0 < b)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * N ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : X → Finset (Fin (permanentCount + sampleCount + 1)))
    (hchecks : ∀ x, approved x = true → Checks μ active (reserve x) (cuts x) (t x) eta (selected x) N)
    (hsubset : ∀ x, approved x = true → domain (reserve x).cells ⊆ domain samplingBuffer)
    (hmass : ∀ x, approved x = true → ∀ i,
      q / 2 * (μ (active i)).real (domain samplingBuffer) ≤ (μ (active i)).real (domain (reserve x).cells)) :
    (parameterLaw.prod (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))))
      {p | approved p.1 = true ∧
        (run policy (tasks active (reserve p.1) (cuts p.1) (t p.1) eta lam)
          (preparedInitial active (reserve p.1) (cuts p.1) (t p.1) eta (approved p.1)) p.2).2.stopped = true} ≤
      ENNReal.ofReal (8 * ((k : ℝ) * eta) * N / lam) +
        ENNReal.ofReal (16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / (q * b * (sampleCount + 1 : ℕ))) := by
  let jobs (x : X) := tasks active (reserve x) (cuts x) (t x) eta lam
  let initial (x : X) := preparedInitial active (reserve x) (cuts x) (t x) eta (approved x)
  let starts := Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))
  let estimated : Set (X × (Fin k → UpperCircular.Circle)) := {p | p.2 ∈ UpperEnvelopeLoop.bad policy (jobs p.1)
    (table active (reserve p.1) (cuts p.1)) (uniformCells (cell (domain errorDomain) (cuts p.1))) id lam (initial p.1)}
  let interpolated : Set (X × (Fin k → UpperCircular.Circle)) := {p | BadSupportedRecordedUnion
    (fun i => μ (active i)) (fun i => (μ (active i)).real (domain errorDomain)) errorDomain
    (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b}
  have hfullsize : (k : ℝ)^2 ≤ lam := by linarith
  have hmono (x : X) : Monotone (cuts x) := by rw [hgrid]; exact sorted_monotone _
  have he : (parameterLaw.prod starts) estimated ≤ ENNReal.ofReal (8 * ((k : ℝ) * eta) * N / lam) :=
    UpperPreparedEnvelopeFamily.probability_le μ policy hpolicy hmeas active hinj parameterLaw errorDomain reserve
      hreserve hdomain cuts hcuts hmono t ht approved happroved eta lam N heta hlam hN hfullsize hmargin selected hchecks
  have hjobs (j : Fin k) : Measurable (fun x => jobs x j) :=
    (measurable_pi_apply j).comp
      (tasks_measurable active reserve cuts t (fun _ => eta) (fun _ => lam) hreserve hcuts ht measurable_const measurable_const)
  have hinitial : Measurable initial := preparedInitial_measurable active reserve cuts t eta approved hreserve hcuts ht happroved
  have hprepare (x : X) (_ : ValidSamples (samples x)) (hopen : (initial x).stopped = false) :
      PreparationFacts μ (Finset.univ.image active) (domain samplingBuffer) q (jobs x)
        (initial x).current (domain errorDomain)
        (pending (cell (domain (reserve x).cells) (cuts x)) (table active (reserve x) (cuts x)) (t x) eta) := by
    have hx : approved x = true := by
      by_contra hx
      simp [initial, preparedInitial, hx] at hopen
    have hc := hchecks x hx
    have h := UpperCorrectionReady.preparationFacts μ active hinj (reserve x) hc.wellFormed
      (cuts x) hc.zero hc.one hc.monotone hc.separated hc.positive (t x) eta lam heta hc.small hc.targets hc.sum hfullsize
      (domain samplingBuffer) (hsubset x hx) q (hmass x hx) hmargin
    simpa only [initial, preparedInitial, hx, ite_true, hdomain x, activeSet, jobs] using h
  have hi : (parameterLaw.prod starts) interpolated ≤
      ENNReal.ofReal (16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / (q * b * (sampleCount + 1 : ℕ))) := by
    simpa only [Fintype.card_fin] using
      prepared_loop_interpolation_probability μ active (fun i => (μ (active i)).real (domain errorDomain))
        samplingBuffer errorDomain hpositive permanent hpermanent sampleLaw hsupport hmixture parameterLaw samples hsamples
        policy hpolicy hmeas jobs hjobs (fun _ => id) (fun _ _ => Function.injective_id) (fun _ _ _ => rfl)
        initial hinitial (fun x => pending (cell (domain (reserve x).cells) (cuts x))
          (table active (reserve x) (cuts x)) (t x) eta) q b hq hb hprepare
  have hcover : {p : X × (Fin k → UpperCircular.Circle) | approved p.1 = true ∧
      (run policy (jobs p.1) (initial p.1) p.2).2.stopped = true} ⊆ estimated ∪ interpolated := by
    rintro p ⟨hx, hreject⟩
    have hinit : initial p.1 = startState active (reserve p.1) (cuts p.1) (t p.1) eta := by
      simp only [initial, preparedInitial, hx, ite_true]
    rw [hinit] at hreject
    have hc := hchecks p.1 hx
    have h := UpperCorrectionFailure.rejection_subset μ policy hpolicy active hinj (reserve p.1) (cuts p.1) (t p.1)
      eta lam N b heta hlam.le hb.le hsize hquarter hmargin (selected p.1) hc hreject
    rcases h with he | hi
    · left
      change p.2 ∈ UpperEnvelopeLoop.bad policy (jobs p.1) _ _ id lam (initial p.1)
      simpa only [jobs, hinit, hdomain p.1] using he
    · right
      change BadSupportedRecordedUnion _ _ _ _ _ b
      simp only [Set.mem_ofPred_eq] at hi
      have hrows (normalizer : Fin k → ℝ) (grid : Fin (permanentCount + sampleCount + 2) → ℝ) :
          physicalRows (fun i => μ (active i)) normalizer (reserve p.1).cells grid =
          physicalRows (fun i => μ (active i)) normalizer errorDomain grid := by
        funext i e
        change (μ (active i)).real (cell (domain (reserve p.1).cells) grid e) / normalizer i = _
        rw [hdomain p.1]
        rfl
      simp only [BadSupportedRecordedUnion, hrows] at hi
      simpa only [BadSupportedRecordedUnion, jobs, hinit, hdomain p.1, hgrid p.1] using hi
  calc
    _ ≤ (parameterLaw.prod starts) (estimated ∪ interpolated) := measure_mono hcover
    _ ≤ (parameterLaw.prod starts) estimated + (parameterLaw.prod starts) interpolated := measure_union_le _ _
    _ ≤ _ := add_le_add he hi

end EnvyFreeResearch.Full.UpperPreparedCorrectionProbability
