import EnvyFreeResearch.Full.UpperAggregateInterpolationEndpoints
import EnvyFreeResearch.Full.UpperAggregateInterpolationPredictable

/-!
# Endpoint charges of the actual stopped correction loop

The transition below is exactly `UpperCorrectionLoop.step`. A proposal is
charged whenever its preceding state is not stopped, including the first
rejection. Subsequent frozen states have zero charge and zero allowance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperCorrectionExecution UpperCorrectionLoop UpperDomainDifference
  UpperRecordedDomain UpperCircularStage UpperStageMeasurable UpperUnionCircular Chores

variable {n : ℕ}

abbrev Start := UpperCircular.Circle

def loopTransition {m : ℕ} (policy : Policy n) (jobs : Fin m → Job n)
    (i : Fin m) (state : LoopState n) (start : Start) : LoopState n :=
  (UpperCorrectionLoop.step policy state (jobs i, start)).2

def proposalCharge (policy : Policy n) (job : Job n) (u : ℝ → ℝ≥0∞)
    (state : LoopState n) (start : Start) : ℝ≥0∞ :=
  if state.stopped then 0 else
    let r := descriptor policy state.current job.owner job.deficit start
    u r.first + u r.last

/-- Every reported rejection flag corresponds to the very same preceding
state used by the charge calculation. -/
theorem run_rejection_eq_reached {m : ℕ} (policy : Policy n) (jobs : Fin m → Job n)
    (state : LoopState n) (tape : Fin m → Start) (i : Fin m) :
    (UpperCorrectionLoop.run policy jobs state tape).1 i =
      (UpperCorrectionLoop.step policy (reached (loopTransition policy jobs) state tape i)
        (jobs i, tape i)).1 := by
  induction m generalizing state with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun j => jobs j.succ)
        (UpperCorrectionLoop.step policy state (jobs 0, tape 0)).2
        (fun j => tape j.succ) j

/-- A rejecting proposal retains both charges; the stopped flag is set only
after these endpoints have been produced and recorded. -/
theorem rejecting_proposal_counted (policy : Policy n) (job : Job n) (u : ℝ → ℝ≥0∞)
    (state : LoopState n) (start : Start) (hopen : state.stopped = false)
    (hreject : accepts job state.current
      (execute policy state.current job.owner job.deficit start).2 = false) :
    proposalCharge policy job u state start =
      u (descriptor policy state.current job.owner job.deficit start).first +
      u (descriptor policy state.current job.owner job.deficit start).last ∧
    (UpperCorrectionLoop.step policy state (job, start)).2.stopped = true ∧
    (UpperCorrectionLoop.step policy state (job, start)).2.current.history =
      (execute policy state.current job.owner job.deficit start).2.history := by
  simp [proposalCharge, UpperCorrectionLoop.step, hopen, hreject]

theorem stopped_proposal_zero (policy : Policy n) (job : Job n) (u : ℝ → ℝ≥0∞)
    (state : LoopState n) (start : Start) (hstop : state.stopped = true) :
    proposalCharge policy job u state start = 0 := by simp [proposalCharge, hstop]

theorem loopTransition_measurable {m : ℕ} (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (jobs : Fin m → Job n) (i : Fin m) :
    Measurable (Function.uncurry (loopTransition policy jobs i)) :=
  measurable_snd.comp ((UpperCorrectionLoop.step_measurable policy hpolicy).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))

theorem proposalCharge_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (job : Job n) (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    Measurable (Function.uncurry (proposalCharge policy job u)) := by
  have hr : Measurable (fun p : LoopState n × Start =>
      descriptor policy p.1.current job.owner job.deficit p.2) :=
    descriptor_measurable policy hpolicy _ _ _ _
      (loop_current_measurable.comp measurable_fst) measurable_const measurable_const measurable_snd
  exact measurable_const.ite
    (measurableSet_eq_fun (loop_stopped_measurable.comp measurable_fst) measurable_const)
    ((hu.comp (correction_first_measurable.comp hr)).add
      (hu.comp (correction_last_measurable.comp hr)))

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

/-- Per-reached-state domination for the actual transaction, using raw oracle
units and the actual history-prefix cache. -/
theorem proposalCharge_bound (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (job : Job n) (u : ℝ → ℝ≥0∞) (hu : Measurable u)
    (state : LoopState n) (hstate : WellFormed μ state.current)
    (B : Set ℝ) (hsub : domain state.current.cells ⊆ B)
    (lower : ℝ) (hlower : 0 < lower)
    (hsupply : lower ≤ (μ job.owner).real (domain state.current.cells)) :
    (∫⁻ start, proposalCharge policy job u state start ∂(volume : Measure Start)) ≤
      ∫⁻ z, u z ∂(if state.stopped then 0 else
        (2 * ENNReal.ofReal (1 / lower)) • (μ job.owner).restrict B) := by
  by_cases hstop : state.stopped = true
  · simp [proposalCharge, hstop]
  · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
    simp only [proposalCharge, hopen, Bool.false_eq_true, ↓reduceIte,
      descriptor, recordedCorrection]
    rw [total_correct μ state.current hstate job.owner, lintegral_smul_measure]
    exact endpoint_charge_le μ policy hpolicy hmeas state.current.history job.owner
      (values state.current job.owner) state.current.cells hstate.1 hstate.2.1
      (values_correct μ state.current hstate job.owner) (hlower.trans_le hsupply)
      (amount job.deficit ((μ job.owner).real (domain state.current.cells))) u hu B hsub lower hlower hsupply

/-- Unconditional endpoint-charge bound for the real stopped loop. The
invariant and supply premises are local reached-state facts; the aggregate
expectation and stopping treatment are conclusions of the fresh-tape proof. -/
theorem loop_endpoint_expectation {m : ℕ} (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (jobs : Fin m → Job n) (u : ℝ → ℝ≥0∞) (hu : Measurable u)
    (B : Set ℝ) (lower : Fin m → ℝ) (hlower : ∀ i, 0 < lower i)
    (Safe : Fin (m + 1) → LoopState n → Prop)
    (hpreserve : ∀ i state start, Safe i.castSucc state →
      Safe i.succ (loopTransition policy jobs i state start))
    (hsupply : ∀ i state, Safe i.castSucc state → state.stopped = false →
      WellFormed μ state.current ∧ domain state.current.cells ⊆ B ∧
      lower i ≤ (μ (jobs i).owner).real (domain state.current.cells))
    (state : LoopState n) (hstate : Safe 0 state) (base : Measure ℝ) (Λ : ℝ≥0∞)
    (hbudget : (∑ i, (2 * ENNReal.ofReal (1 / lower i)) • (μ (jobs i).owner).restrict B) ≤ Λ • base) :
    (∫⁻ tape, tapeTotal (loopTransition policy jobs)
      (fun i => proposalCharge policy (jobs i) u) state tape
      ∂Measure.pi (fun _ : Fin m => (volume : Measure Start))) ≤ Λ * ∫⁻ z, u z ∂base := by
  let K (i : Fin m) (state : LoopState n) : Measure ℝ := if state.stopped then 0 else
    (2 * ENNReal.ofReal (1 / lower i)) • (μ (jobs i).owner).restrict B
  apply aggregate_lintegral_bound (fun _ : Fin m => (volume : Measure Start))
    (loopTransition policy jobs) (fun i => proposalCharge policy (jobs i) u) K u
    (loopTransition_measurable policy hmeas jobs)
    (fun i => proposalCharge_measurable policy hmeas (jobs i) u hu)
    ?_ Safe hpreserve ?_ state hstate base Λ ?_
  · intro i
    have heq : (fun state : LoopState n => ∫⁻ z, u z ∂K i state) =
        (fun state => if state.stopped then 0 else
          ∫⁻ z, u z ∂(2 * ENNReal.ofReal (1 / lower i)) • (μ (jobs i).owner).restrict B) := by
      funext state; cases hs : state.stopped <;> simp [K, hs]
    rw [heq]
    exact measurable_const.ite (measurableSet_eq_fun loop_stopped_measurable measurable_const) measurable_const
  · intro i state hs
    by_cases hstop : state.stopped = true
    · simp [proposalCharge, K, hstop]
    · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
      obtain ⟨hwf, hsub, hmass⟩ := hsupply i state hs hopen
      exact proposalCharge_bound μ policy hpolicy hmeas (jobs i) u hu state hwf B hsub
        (lower i) (hlower i) hmass
  · intro tape
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hbudget
    dsimp only [K]
    split_ifs
    · exact bot_le
    · exact le_rfl

end EnvyFreeResearch.Full.UpperAggregateInterpolation
