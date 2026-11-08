import EnvyFreeResearch.Full.UpperAggregateInterpolationMixture
import EnvyFreeResearch.Full.UpperAggregateInterpolationSupported
import EnvyFreeResearch.Full.UpperCorrectionSupply

/-!
# Concrete preparation checks discharge the reached-supply invariant

The successful-preparation facts are ordinary literal set identities, cached
payment equalities, and scalar budget checks. The existing correction-supply
proof derives initialization, preservation and raw supply from them. If the
preparation branch stops, it produces no endpoint charges; no probability is
conditioned on successful preparation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperCircularStage UpperStageMeasurable UpperCorrectionExecution
  UpperCorrectionLoop UpperGridInterpolation UpperSortedGrid Chores

variable {n m : ℕ}

/-- Concrete checks on the original raw measure/cache data, before fresh
correction starts. This structure does not contain a loop-safety assertion. -/
structure PreparationFacts (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (agents : Finset (Fin n)) (B : Set ℝ) (q : ℝ)
    (jobs : Fin m → Job n) (state : State n) (reserve : Set ℝ) (pending : Fin m → Set ℝ) : Prop where
  wellFormed : WellFormed μ state
  reserve_subset : reserve ⊆ B
  domain_eq : domain state.cells = reserve \ ⋃ j, pending j
  previous : ∀ j i, i ∈ agents → (jobs j).previous i = (μ i).real (pending j)
  budget_cap : ∀ i ∈ agents, (∑ j, ((jobs j).desired i + (jobs j).tolerance i)) < (μ i).real reserve / 8
  reserve_mass : ∀ i ∈ agents, q / 2 * (μ i).real B ≤ (μ i).real reserve
  checked : ∀ j i, i ∈ agents → (jobs j).checked i = true
  nonnegative_budget : ∀ j i, i ∈ agents → 0 ≤ UpperCorrectionSupply.budget (jobs j) i

variable {permanentCount sampleCount stageCount : ℕ}
  {Row Parameter : Type*} [Fintype Row] [Nonempty Row] [MeasurableSpace Parameter]

set_option maxHeartbeats 1200000 in
/-- Full-history aggregate interpolation after a possibly failing preparation
branch. The fixed error domain is the actual reserve. Concrete preparation
checks discharge the reached-supply invariant using the actual acceptance test. -/
theorem prepared_loop_interpolation_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (normalizer : Row → ℝ) (samplingBuffer errorDomain : List Component)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain samplingBuffer))
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (hmixture : sampleLaw = UpperMixtureSampling.mixture μ active samplingBuffer)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (samples : Parameter → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy)
    (jobs : Parameter → Fin stageCount → Job n) (hjobs : ∀ i, Measurable (fun p => jobs p i))
    (recipient : Parameter → Fin stageCount → Row)
    (hinjective : ∀ p, ValidSamples (samples p) → Function.Injective (recipient p))
    (howner : ∀ p, ValidSamples (samples p) → ∀ i, (jobs p i).owner = active (recipient p i))
    (initial : Parameter → LoopState n) (hinitial : Measurable initial)
    (pending : Parameter → Fin stageCount → Set ℝ)
    (q b : ℝ) (hq : 0 < q) (hb : 0 < b)
    (hprepare : ∀ p, ValidSamples (samples p) → (initial p).stopped = false →
      PreparationFacts μ (Finset.univ.image active) (domain samplingBuffer) q (jobs p)
        (initial p).current (domain errorDomain) (pending p)) :
    (parameterLaw.prod (Measure.pi (fun _ : Fin stageCount => (volume : Measure Start))))
      {p | BadSupportedRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b} ≤
      ENNReal.ofReal (16 * (Fintype.card Row : ℝ) * ((Fintype.card Row : ℝ) - 1) * (1 + b) /
        (q * b * (sampleCount + 1 : ℕ))) := by
  simp_rw [badSupportedRecordedUnion_iff]
  let agents : Finset (Fin n) := Finset.univ.image active
  let floor (i : Fin n) := 7 / 8 * (μ i).real (domain errorDomain)
  let Safe (p : Parameter) (time : Fin (stageCount + 1)) (state : LoopState n) :=
    state.stopped = true ∨ ((initial p).stopped = false ∧
      UpperCorrectionSupply.Safe μ agents (domain samplingBuffer) floor (jobs p) time state)
  have hactive (r : Row) : active r ∈ agents := Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have hpos (i : Fin n) (hi : i ∈ agents) : 0 < (μ i).real (domain samplingBuffer) := by
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    exact hpositive r
  have hfloor (p : Parameter) (hs : ValidSamples (samples p))
      (hopen : (initial p).stopped = false) (i : Fin n) (hi : i ∈ agents) : 0 < floor i := by
    have hf := hprepare p hs hopen
    have hr : 0 < (μ i).real (domain errorDomain) :=
      (mul_pos (div_pos hq (by norm_num)) (hpos i hi)).trans_le (hf.reserve_mass i hi)
    exact mul_pos (by norm_num) hr
  apply actual_loop_mixture_interpolation_probability μ active normalizer samplingBuffer errorDomain hpositive
    permanent hpermanent sampleLaw hsupport hmixture parameterLaw samples hsamples
    policy hpolicy hmeas jobs hjobs recipient hinjective howner initial hinitial q b hq hb Safe ?_ ?_ ?_
  · intro p hs time state start hsafe
    rcases hsafe with hstop | ⟨hopen, hsafe⟩
    · left
      change (UpperCorrectionLoop.step policy state (jobs p time, start)).2.stopped = true
      rw [UpperCorrectionLoop.step_stopped policy state (jobs p time, start) hstop]
      exact hstop
    · right
      refine ⟨hopen, ?_⟩
      have hf := hprepare p hs hopen
      exact UpperCorrectionSupply.safe_step μ policy hpolicy agents (domain samplingBuffer) floor
        (hfloor p hs hopen) (jobs p) (fun i => by rw [howner p hs i]; exact hactive _)
        hf.checked hf.nonnegative_budget time state start hsafe
  · intro p hs time state hsafe hopenstate
    rcases hsafe with hstop | ⟨hopen, hsafe⟩
    · simp [hopenstate] at hstop
    · have hf := hprepare p hs hopen
      refine ⟨hsafe.1, hsafe.2.1, ?_⟩
      exact UpperCorrectionSupply.raw_supply μ agents (domain samplingBuffer) (domain errorDomain)
        (jobs p) time.castSucc state hsafe hf.nonnegative_budget q hq.le hf.reserve_mass
        (jobs p time).owner (by rw [howner p hs time]; exact hactive _)
  · intro p hs
    by_cases hstop : (initial p).stopped = true
    · exact Or.inl hstop
    · have hopen : (initial p).stopped = false := Bool.eq_false_iff.mpr hstop
      refine Or.inr ⟨hopen, ?_⟩
      have hf := hprepare p hs hopen
      exact UpperCorrectionSupply.safe_initial μ agents (domain samplingBuffer) (domain errorDomain)
        hf.reserve_subset (jobs p) (pending p) (initial p).current hf.wellFormed
        hf.domain_eq hf.previous hf.budget_cap

end EnvyFreeResearch.Full.UpperAggregateInterpolation
