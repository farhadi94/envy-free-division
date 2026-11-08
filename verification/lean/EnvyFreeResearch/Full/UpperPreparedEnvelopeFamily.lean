import EnvyFreeResearch.Full.UpperPreparedEnvelopeMean

/-! Original-parameter averaging of the concrete correction envelope.
Preparation rejection stops before corrections. The original parameter law
is arbitrary: no law conditioned on successful preparation is introduced. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperPreparedEnvelopeFamily

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperCorrectionExecution
  UpperCorrectionLoop UpperCorrectionSetup UpperEnvelope UpperCircularStage UpperStageMeasurable
  UpperEnvelopeFamily UpperPreparedEnvelopeMean UpperAggregateInterpolation

variable {n k m : ℕ} [Nonempty (Fin k)] {X : Type*} [MeasurableSpace X]

def preparedInitial (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta : ℝ) (approved : Bool) : LoopState n :=
  if approved then startState active reserve cuts t eta else ⟨reserve, true, []⟩

theorem preparedInitial_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta : ℝ) (approved : X → Bool)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (happroved : Measurable approved) :
    Measurable (fun z => preparedInitial active (reserve z) (cuts z) (t z) eta (approved z)) :=
  (startState_measurable active reserve cuts t (fun _ => eta) hreserve hcuts ht measurable_const).ite
    (measurableSet_eq_fun happroved measurable_const)
    (loop_mk_measurable reserve (fun _ => true) (fun _ => []) hreserve measurable_const measurable_const)

theorem bad_empty_of_stopped (policy : Policy n) (jobs : Fin k → Job n)
    (a : Fin k → Fin (m + 1) → ℝ) (rho : Fin (m + 1) → Measure ℝ)
    (initial : LoopState n) (lam : ℝ) (hstop : initial.stopped = true) :
    UpperEnvelopeLoop.bad policy jobs a rho id lam initial = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro tape htape
  obtain ⟨j, hj, _⟩ := htape
  have hp (i : Fin k) (state : LoopState n) (draw : UpperCircular.Circle)
      (hs : state.stopped = true) : (loopTransition policy jobs i state draw).stopped = true := by
    simpa [loopTransition, step_stopped policy state _ hs] using hs
  have hs := UpperEnvelopeLoop.reached_invariant (loopTransition policy jobs)
    (fun _ state => state.stopped = true) hp initial tape hstop j
  simp only [hj, Bool.false_eq_true] at hs

/-- This bound averages the actual concrete jobs and complete initial history
over the original preparation law, including all rejected preparations.
Only explicit arithmetic/geometry checks are required on approved inputs. -/
theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (parameterLaw : Measure X) [IsProbabilityMeasure parameterLaw]
    (buffer : List Component) (reserve : X → State n) (hreserve : Measurable reserve)
    (hdomain : ∀ x, domain (reserve x).cells = domain buffer)
    (cuts : X → Fin (m + 2) → ℝ) (hcuts : ∀ e, Measurable (fun x => cuts x e))
    (hmono : ∀ x, Monotone (cuts x)) (t : X → Fin k → ℝ)
    (ht : ∀ j, Measurable (fun x => t x j))
    (approved : X → Bool) (happroved : Measurable approved)
    (eta lam N : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N)
    (hsize : (k : ℝ)^2 ≤ lam) (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : X → Finset (Fin (m + 1)))
    (hchecks : ∀ x, approved x = true → Checks μ active (reserve x) (cuts x) (t x) eta (selected x) N) :
    (parameterLaw.prod (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))))
      {p | p.2 ∈ UpperEnvelopeLoop.bad policy (tasks active (reserve p.1) (cuts p.1) (t p.1) eta lam)
        (table active (reserve p.1) (cuts p.1)) (uniformCells (cell (domain buffer) (cuts p.1))) id lam
        (preparedInitial active (reserve p.1) (cuts p.1) (t p.1) eta (approved p.1))} ≤
      ENNReal.ofReal (8 * ((k : ℝ) * eta) * N / lam) := by
  let jobs (x : X) := tasks active (reserve x) (cuts x) (t x) eta lam
  let a (x : X) := table active (reserve x) (cuts x)
  let rho (x : X) := uniformCells (cell (domain buffer) (cuts x))
  let foreign (x : X) (j : Fin k) := envelope (a x) (rho x) j
  let initial (x : X) := preparedInitial active (reserve x) (cuts x) (t x) eta (approved x)
  let starts := Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))
  let charge (p : X × (Fin k → UpperCircular.Circle)) := totalCharge policy (jobs p.1) (foreign p.1) (initial p.1) p.2
  have hjobs (j : Fin k) : Measurable (fun x => jobs x j) :=
    (measurable_pi_apply j).comp
      (tasks_measurable active reserve cuts t (fun _ => eta) (fun _ => lam) hreserve hcuts ht measurable_const measurable_const)
  have hinitial : Measurable initial := preparedInitial_measurable active reserve cuts t eta approved hreserve hcuts ht happroved
  have hmass (j : Fin k) : Measurable (fun p : X × Component => mass (foreign p.1 j) p.2) :=
    UpperEnvelopeMeasurable.envelope_mass_measurable buffer cuts hcuts hmono a
      (table_measurable active reserve cuts hreserve hcuts) j
  have hcharge : Measurable charge := totalCharge_measurable policy hmeas jobs hjobs foreign hmass initial hinitial
  have hlocal (x : X) (hx : approved x = true) :=
    mean_and_bad μ policy hpolicy hmeas active hinj (reserve x) (cuts x) (t x)
      eta lam N heta hlam hN hsize hmargin (selected x) (hchecks x hx)
  have hfiber (x : X) : (∫⁻ tape, charge (x, tape) ∂starts) ≤ ENNReal.ofReal (2 * ((k : ℝ) * eta) * N) := by
    by_cases hx : approved x = true
    · simpa only [charge, jobs, foreign, a, rho, initial, preparedInitial, hx, ite_true, hdomain x, starts]
        using (hlocal x hx).1
    · have hstop : (initial x).stopped = true := by simp [initial, preparedInitial, hx]
      simp only [charge, totalCharge_stopped policy (jobs x) (foreign x) (initial x) _ hstop, lintegral_zero]
      exact zero_le
  have hmean : (∫⁻ p, charge p ∂parameterLaw.prod starts) ≤ ENNReal.ofReal (2 * ((k : ℝ) * eta) * N) := by
    rw [lintegral_prod _ hcharge.aemeasurable]
    calc
      _ ≤ ∫⁻ _ : X, ENNReal.ofReal (2 * ((k : ℝ) * eta) * N) ∂parameterLaw := lintegral_mono hfiber
      _ = _ := by simp
  have hbad : {p : X × (Fin k → UpperCircular.Circle) |
      p.2 ∈ UpperEnvelopeLoop.bad policy (jobs p.1) (a p.1) (rho p.1) id lam (initial p.1)} ⊆
      {p | ENNReal.ofReal (lam / 4) ≤ charge p} := by
    intro p hp
    change p.2 ∈ UpperEnvelopeLoop.bad policy (jobs p.1) (a p.1) (rho p.1) id lam (initial p.1) at hp
    by_cases hx : approved p.1 = true
    · have h := (hlocal p.1 hx).2
      have hi : initial p.1 = startState active (reserve p.1) (cuts p.1) (t p.1) eta := by
        simp [initial, preparedInitial, hx]
      change ENNReal.ofReal (lam / 4) ≤ charge p
      simpa only [Set.mem_setOf_eq, charge, jobs, foreign, a, rho, hi, hdomain p.1] using
        h (by simpa only [jobs, a, rho, hi, hdomain p.1] using hp)
    · have hstop : (initial p.1).stopped = true := by simp [initial, preparedInitial, hx]
      rw [bad_empty_of_stopped policy (jobs p.1) (a p.1) (rho p.1) (initial p.1) lam hstop] at hp
      exact False.elim hp
  have hthreshold : 0 < lam / 4 := div_pos hlam (by norm_num)
  calc
    _ ≤ (parameterLaw.prod starts) {p | ENNReal.ofReal (lam / 4) ≤ charge p} := measure_mono hbad
    _ ≤ (∫⁻ p, charge p ∂parameterLaw.prod starts) / ENNReal.ofReal (lam / 4) :=
      meas_ge_le_lintegral_div hcharge.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * ((k : ℝ) * eta) * N) / ENNReal.ofReal (lam / 4) := by gcongr
    _ = ENNReal.ofReal ((2 * ((k : ℝ) * eta) * N) / (lam / 4)) := (ENNReal.ofReal_div_of_pos hthreshold).symm
    _ = _ := by congr 1; field_simp; ring

end EnvyFreeResearch.Full.UpperPreparedEnvelopeFamily
