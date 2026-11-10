import EnvyFreeResearch.Full.UpperEnvelopeCharge
import EnvyFreeResearch.Full.UpperAggregateInterpolationLoop

/-! Fresh conditional probability bounds for a literal correction attempt.
The state includes the entire preceding answered-query history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperCorrectionChance
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperRecordedDomain
  UpperDomainDifference UpperStageMeasurable UpperEnvelopeCharge UpperAggregateInterpolation
abbrev Circle := UpperCircular.Circle
variable {n : ℕ}

def endpointBad (policy : Policy n) (job : Job n) (bad : Set ℝ)
    (s : LoopState n) (start : Circle) : Bool :=
  if s.stopped then false else
    decide ((descriptor policy s.current job.owner job.deficit start).first ∈ bad ∨
      (descriptor policy s.current job.owner job.deficit start).last ∈ bad)

theorem endpointBad_measurable (policy : Policy n) (hp : MeasurablePolicy policy)
    (job : Job n) (bad : Set ℝ) (hb : MeasurableSet bad) :
    Measurable (Function.uncurry (endpointBad policy job bad)) := by
  have hd : Measurable (fun p : LoopState n × Circle =>
      descriptor policy p.1.current job.owner job.deficit p.2) :=
    descriptor_measurable policy hp _ _ _ _
      (loop_current_measurable.comp measurable_fst) measurable_const measurable_const measurable_snd
  have he : MeasurableSet {p : LoopState n × Circle |
      (descriptor policy p.1.current job.owner job.deficit p.2).first ∈ bad ∨
      (descriptor policy p.1.current job.owner job.deficit p.2).last ∈ bad} :=
    (hb.preimage (correction_first_measurable.comp hd)).union
      (hb.preimage (correction_last_measurable.comp hd))
  exact measurable_const.ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp measurable_fst) measurable_const)
    (decide_measurable _ he)

theorem endpointBad_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (job : Job n) (bad : Set ℝ) (hb : MeasurableSet bad)
    (s : LoopState n) (hs : WellFormed μ s.current)
    (B : Set ℝ) (hsub : domain s.current.cells ⊆ B)
    (lower : ℝ) (hlower : 0 < lower) (hsupply : lower ≤ (μ job.owner).real (domain s.current.cells)) :
    (volume : Measure Circle) {start | endpointBad policy job bad s start = true} ≤
      (2 * ENNReal.ofReal (1 / lower)) * ((μ job.owner).restrict B) bad := by
  let u : ℝ → ℝ≥0∞ := bad.indicator (fun _ => 1)
  have hu : Measurable u := measurable_const.indicator hb
  have hcharge : Measurable (fun start : Circle => proposalCharge policy job u s start) :=
    (proposalCharge_measurable policy hm job u hu).of_uncurry_left
  have hsubevent : {start | endpointBad policy job bad s start = true} ⊆
      {start | (1 : ℝ≥0∞) ≤ proposalCharge policy job u s start} := by
    intro start ht
    change (1 : ℝ≥0∞) ≤ proposalCharge policy job u s start
    by_cases hstop : s.stopped = true
    · simp [endpointBad, hstop] at ht
    · have ho : s.stopped = false := Bool.eq_false_iff.mpr hstop
      simp only [endpointBad, ho, Bool.false_eq_true, ite_false, decide_eq_true_eq] at ht
      simp only [proposalCharge, ho, Bool.false_eq_true, ite_false]
      rcases ht with hfirst | hlast
      · simp only [u, Set.indicator_of_mem hfirst]
        exact le_add_of_nonneg_right zero_le
      · simp only [u, Set.indicator_of_mem hlast]
        exact le_add_of_nonneg_left zero_le
  have hc := proposalCharge_bound μ policy hp hm job u hu s hs B hsub lower hlower hsupply
  by_cases hstop : s.stopped = true
  · simp [endpointBad, hstop]
  · have ho : s.stopped = false := Bool.eq_false_iff.mpr hstop
    simp only [ho, Bool.false_eq_true, ite_false, lintegral_smul_measure] at hc
    rw [lintegral_indicator_const hb, one_mul] at hc
    calc
      _ ≤ (volume : Measure Circle) {start | (1 : ℝ≥0∞) ≤ proposalCharge policy job u s start} := measure_mono hsubevent
      _ ≤ (∫⁻ start : Circle, proposalCharge policy job u s start ∂volume) / 1 :=
        meas_ge_le_lintegral_div hcharge.aemeasurable (by norm_num) (by norm_num)
      _ ≤ _ := by simpa only [div_one, smul_eq_mul] using hc

theorem envelope_probability (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (job : Job n) (s : LoopState n)
    (hs : s.stopped = false → WellFormed μ s.current)
    (eps scale N lam : ℝ) (heps : 0 ≤ eps) (hscale : 0 < scale) (hN : 0 ≤ N) (hlam : 0 < lam)
    (hdeficit : job.deficit = eps * scale)
    (hfit : s.stopped = false → eps * scale ≤ (μ job.owner).real (domain s.current.cells))
    (hsupply : s.stopped = false → scale / 2 ≤ (μ job.owner).real (domain s.current.cells))
    (foreign : Measure ℝ) [IsFiniteMeasure foreign] [NullSingletonClass foreign]
    (hforeign : s.stopped = false → foreign.real (domain s.current.cells) ≤ N) :
    (volume : Measure Circle) {start | ENNReal.ofReal (lam / 4) ≤ charge foreign policy job s start} ≤
      ENNReal.ofReal (8 * eps * N / lam) := by
  have hc := charge_expectation_le μ policy hp hm job s hs eps scale N heps hscale hN
    hdeficit hfit hsupply foreign hforeign
  have hmeas : Measurable (fun start : Circle => charge foreign policy job s start) :=
    (charge_measurable foreign policy hm job).of_uncurry_left
  have ht : 0 < lam / 4 := by positivity
  calc
    _ ≤ (∫⁻ start : Circle, charge foreign policy job s start ∂volume) / ENNReal.ofReal (lam/4) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2*eps*N) / ENNReal.ofReal (lam/4) := by gcongr
    _ = ENNReal.ofReal ((2*eps*N)/(lam/4)) := (ENNReal.ofReal_div_of_pos ht).symm
    _ = _ := by congr 1; field_simp; ring

end EnvyFreeResearch.Full.RefinedUpperCorrectionChance
