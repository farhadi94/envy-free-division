import EnvyFreeResearch.Full.UpperSamplingRecords
import EnvyFreeResearch.Full.UpperMixtureSampling
import EnvyFreeResearch.Full.UpperCorrectionExecution

/-!
# Actual sampled grid records and physical cache refinement

The final query history records every generated endpoint for every original
observer. Refinement at those literal coordinates preserves the physical
buffer and builds a correctly cached physical representation. Logical grid
indices remain separate from these possibly more numerous physical atoms.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperGridRecords

open UpperRecordedDomain UpperDomainDifference UpperEndpointCache UpperCircularStage
  UpperUnionSampling UpperSamplingRecords UpperCorrectionExecution Chores

variable {n : ℕ}

def HasEndpoint (history : History n) (point : ℝ) : Prop :=
  ∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 point, answer) ∈ history

theorem hasEndpoint_mono {before after : History n} {point : ℝ}
    (h : HasEndpoint before point) (hextend : before ⊆ after) : HasEndpoint after point := by
  intro i
  obtain ⟨answer, ha⟩ := h i
  exact ⟨answer, hextend ha⟩

/-- Induction on the actual sequential run propagates every earlier endpoint
record into the final history, including through later adaptive replies. -/
theorem run_records {Draw : Type*} (step : History n → Draw → ℝ × History n)
    (Good : History n → Prop)
    (hstep : ∀ history, Good history → ∀ draw,
      let next := step history draw
      Good next.2 ∧ history ⊆ next.2 ∧ next.1 ∈ Icc (0 : ℝ) 1 ∧ HasEndpoint next.2 next.1)
    (m : ℕ) (history : History n) (hgood : Good history) (draw : Fin m → Draw) :
    let result := UpperFreshSamples.run step m history draw
    Good result.2 ∧ history ⊆ result.2 ∧
      ∀ i, result.1 i ∈ Icc (0 : ℝ) 1 ∧ HasEndpoint result.2 (result.1 i) := by
  induction m generalizing history with
  | zero => exact ⟨hgood, fun _ h => h, fun i => Fin.elim0 i⟩
  | succ m ih =>
    have hfirst := hstep history hgood (draw 0)
    have hrest := ih (step history (draw 0)).2 hfirst.1 (fun i => draw i.succ)
    refine ⟨hrest.1, fun _ h => hrest.2.1 (hfirst.2.1 h), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hfirst.2.2.1, hasEndpoint_mono hfirst.2.2.2 hrest.2.1⟩
    · exact hrest.2.2 j

section Sampling

variable {Agent : Type*} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (cache : Agent → Component → ℝ) (cells : List Component)
  (hdisjoint : DisjointComponents cells)
  (hcache : ∀ a c, c ∈ cells → cache a c = mass (μ (active a)) c)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells))

include hpolicy hdisjoint hcache hpositive

theorem mixture_run_records (m : ℕ) (history : History n)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cells history)
    (draw : Fin m → Agent × I) :
    let result := UpperFreshSamples.run (UpperMixtureSampling.sample μ policy active cache cells) m history draw
    Truthful μ result.2 ∧ RecordedHistory cells result.2 ∧ history ⊆ result.2 ∧
      ∀ i, result.1 i ∈ Icc (0 : ℝ) 1 ∧ HasEndpoint result.2 (result.1 i) := by
  have hstep : ∀ h, Truthful μ h ∧ RecordedHistory cells h → ∀ d : Agent × I,
      let next := UpperMixtureSampling.sample μ policy active cache cells h d
      (Truthful μ next.2 ∧ RecordedHistory cells next.2) ∧ h ⊆ next.2 ∧
        next.1 ∈ Icc (0 : ℝ) 1 ∧ HasEndpoint next.2 next.1 := by
    intro h hh d
    have hr := sampleExecution_all_records μ policy hpolicy h (active d.1) (cache d.1) cells
      hdisjoint hh.1 hh.2 (hcache d.1) (hpositive d.1) d.2
    exact ⟨⟨hr.2.1, recordedHistory_mono cells hh.2 hr.2.2.1⟩, hr.2.2.1, hr.1, hr.2.2.2⟩
  have h := run_records _ (fun h => Truthful μ h ∧ RecordedHistory cells h) hstep m history
    ⟨htruth, hrecorded⟩ draw
  exact ⟨h.1.1, h.1.2, h.2⟩

end Sampling

def refineEndpoints (cells : List Component) (points : List ℝ) : List Component :=
  points.foldl (fun cs p => refineAt p cs) cells

theorem refineEndpoints_domain (cells : List Component) (points : List ℝ) :
    domain (refineEndpoints cells points) = domain cells := by
  induction points generalizing cells with
  | nil => rfl
  | cons p points ih =>
    change domain (refineEndpoints (refineAt p cells) points) = _
    rw [ih, refineAt_domain]

theorem refineEndpoints_ordered (cells : List Component) (points : List ℝ) (h : Ordered cells) :
    Ordered (refineEndpoints cells points) := by
  induction points generalizing cells with
  | nil => exact h
  | cons p points ih => exact ih _ (refineAt_ordered p cells h)

theorem refineEndpoints_disjoint (cells : List Component) (points : List ℝ) (h : DisjointComponents cells) :
    DisjointComponents (refineEndpoints cells points) := by
  induction points generalizing cells with
  | nil => exact h
  | cons p points ih => exact ih _ (refineAt_disjoint p cells h)

theorem refineEndpoints_recorded (cells : List Component) (points : List ℝ) {p : ℝ}
    (h : Recorded (refineEndpoints cells points) p) : Recorded cells p ∨ p ∈ points := by
  induction points generalizing cells with
  | nil => exact Or.inl h
  | cons q points ih =>
    rcases ih _ h with h | h
    · rcases refineAt_recorded q cells h with rfl | h
      · exact Or.inr (by simp)
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem q h)

/-- The physical refined representation uses only endpoints present in the
actual final history. Every new component cache is then an exact prefix
difference for every original row. -/
theorem refineEndpoints_wellFormed (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (state : State n) (hstate : WellFormed μ state) (points : List ℝ)
    (hpoints : ∀ p ∈ points, HasEndpoint state.history p) :
    WellFormed μ (⟨refineEndpoints state.cells points, state.history⟩ : State n) := by
  refine ⟨refineEndpoints_ordered _ _ hstate.1, refineEndpoints_disjoint _ _ hstate.2.1,
    hstate.2.2.1, ?_⟩
  intro i p hp
  rcases refineEndpoints_recorded _ _ hp with hp | hp
  · exact hstate.2.2.2 i p hp
  · exact hpoints p hp i

variable {X : Type*} [MeasurableSpace X]

theorem refineEndpoints_measurable (cells : X → List Component) (points : X → List ℝ)
    (hcells : Measurable cells) (hpoints : Measurable points) :
    Measurable (fun z => refineEndpoints (cells z) (points z)) :=
  list_foldl_measurable (fun _ cs p => refineAt p cs) cells points
    (refineAt_measurable _ _ (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)) hcells hpoints

end EnvyFreeResearch.Full.UpperGridRecords
