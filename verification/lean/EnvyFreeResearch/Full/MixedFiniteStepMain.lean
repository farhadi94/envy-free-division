import EnvyFreeResearch.Full.MixedRawMain

/-! The hard-input invariant is retained through every finite capture
round. The final success guarantee need only hold on finite-step inputs. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedFiniteStepMain
open Set MeasureTheory OracleProtocol IntervalAllocation MixedFrontier MixedFiniteStep
open MixedPhysicalMain FiniteStepDensity PhysicalReflection
open scoped Classical ENNReal

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ}

abbrev StepState (Agent : Type*) (α : ℝ) := {S : State Agent α // AllStep S}
abbrev StepInput (Agent : Type*) := {I : Input Agent // ∀ i, FiniteStep (I.rows i).density}

theorem left_finite_horizon
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (fuel : ℕ) (ε δ : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hδ : 0 < δ) :
    ∃ S : StepState Agent α, μ (MixedAmplification.capSuccess next S.val fuel ε) ≤ ENNReal.ofReal δ := by
  obtain ⟨T,H,hst,hH,hrem,hp⟩ := MixedAmplification.exists_almost_all_protected (μ := μ)
    next base (MixedViews.concrete_measurable_views next base hnext) (initial Agent α) fuel δ hα hδ
  have hsub : MixedAmplification.capSuccess next T fuel ε ⊆ Hᶜ := by
    intro ω hs hω
    obtain ⟨A,hret,hef⟩ := hs
    exact MixedExecution.protected_failure next T ω fuel ε hn hα.le hε (hp ω hω) A hret hef
  refine ⟨⟨T,hst.steps (initial_allStep Agent α)⟩,?_⟩
  rw [← ofReal_measureReal (μ := μ) (s := MixedAmplification.capSuccess next T fuel ε)]
  exact ENNReal.ofReal_le_ofReal ((measureReal_mono hsub (by finiteness)).trans hrem.le)

theorem right_finite_horizon
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (fuel : ℕ) (ε δ : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hδ : 0 < δ) :
    ∃ S : StepState Agent α, μ (RightmostAmplification.capSuccess next S.val fuel ε) ≤ ENNReal.ofReal δ := by
  obtain ⟨T,H,hst,hH,hrem,hp⟩ := RightmostAmplification.exists_almost_all_protected (μ := μ)
    next base (RightmostViews.concrete_measurable_views next base hnext) (initial Agent α) fuel δ hα hδ
  have hsub : RightmostAmplification.capSuccess next T fuel ε ⊆ Hᶜ := by
    intro ω hs hω
    obtain ⟨A,hret,hef⟩ := hs
    exact RightmostExecution.protected_failure next T ω fuel ε hn hα.le hε (hp ω hω) A hret hef
  refine ⟨⟨T,hst.steps (initial_allStep Agent α)⟩,?_⟩
  rw [← ofReal_measureReal (μ := μ) (s := RightmostAmplification.capSuccess next T fuel ε)]
  exact ENNReal.ofReal_le_ofReal ((measureReal_mono hsub (by finiteness)).trans hrem.le)

theorem left_step_expectations_unbounded
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (ε p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hsuccess : ∀ S : StepState Agent α, ENNReal.ofReal p ≤ μ (MixedSuccess.success next S.val ε)) :
    (⨆ S : StepState Agent α, ∫⁻ ω,
      (queryCost next (IntervalOracle.oracle (MixedExecution.profile S.val)) ω [] : ℝ≥0∞) ∂μ) = ∞ := by
  apply QueryProbability.supremum_expectations_eq_top
    (fun S : StepState Agent α => fun ω => queryCost next (IntervalOracle.oracle (MixedExecution.profile S.val)) ω [])
    (fun S => MixedSuccess.success next S.val ε)
    (fun S => MixedSuccess.actual_cost_measurable next hnext S.val)
    (fun S => MixedSuccess.success_measurable next hnext S.val ε)
    (δ := ENNReal.ofReal (p/2))
  · exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith)
  · exact hsuccess
  · intro fuel
    obtain ⟨S,hS⟩ := left_finite_horizon (μ := μ) next base hnext fuel ε (p/2)
      hn hα hε (by linarith)
    refine ⟨S,?_⟩
    rw [MixedSuccess.success_below_cap]
    exact hS

theorem right_step_expectations_unbounded
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (ε p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hsuccess : ∀ S : StepState Agent α, ENNReal.ofReal p ≤ μ (RightmostSuccess.success next S.val ε)) :
    (⨆ S : StepState Agent α, ∫⁻ ω,
      (queryCost next (RightmostOracle.oracle (RightmostExecution.profile S.val)) ω [] : ℝ≥0∞) ∂μ) = ∞ := by
  apply QueryProbability.supremum_expectations_eq_top
    (fun S : StepState Agent α => fun ω => queryCost next (RightmostOracle.oracle (RightmostExecution.profile S.val)) ω [])
    (fun S => RightmostSuccess.success next S.val ε)
    (fun S => RightmostSuccess.actual_cost_measurable next hnext S.val)
    (fun S => RightmostSuccess.success_measurable next hnext S.val ε)
    (δ := ENNReal.ofReal (p/2))
  · exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith)
  · exact hsuccess
  · intro fuel
    obtain ⟨S,hS⟩ := right_finite_horizon (μ := μ) next base hnext fuel ε (p/2)
      hn hα hε (by linarith)
    refine ⟨S,?_⟩
    rw [RightmostSuccess.success_below_cap]
    exact hS

/-- A public finite-step input class suffices for both root rules. Every
step has a proved finite-breakpoint certificate, including reflection. -/
theorem attempted_expectations_unbounded
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent, ENNReal.ofReal p ≤ μ (success rule next I.val α ε)) :
    (⨆ I : StepInput Agent, MixedAttemptedMain.expectedAttempts μ rule next I.val) = ∞ := by
  cases rule with
  | leftmost =>
    have hs (S : StepState Agent α) :
        ENNReal.ofReal p ≤ μ (MixedSuccess.success next S.val ε) := by
      simpa only [left_success_eq] using hsuccess ⟨stateInput S.val,S.property⟩
    have htop := left_step_expectations_unbounded next base hnext ε p hn hα hε hp hs
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro S
    exact le_iSup_of_le ⟨stateInput S.val,S.property⟩
      (MixedAttemptedMain.expectedCost_le_expectedAttempts μ .leftmost next (stateInput S.val))
  | rightmost =>
    have hstep (S : StepState Agent α) : ∀ i,
        FiniteStep ((reflectedInput S.val).rows i).density :=
      fun i => reflectRow_finiteStep (S.val.rows i) (S.property i)
    have hs (S : StepState Agent α) :
        ENNReal.ofReal p ≤ μ (RightmostSuccess.success next S.val ε) := by
      simpa only [right_success_eq] using hsuccess ⟨reflectedInput S.val,hstep S⟩
    have htop := right_step_expectations_unbounded next base hnext ε p hn hα hε hp hs
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro S
    apply le_iSup_of_le ⟨reflectedInput S.val,hstep S⟩
    have h := MixedAttemptedMain.expectedCost_le_expectedAttempts μ .rightmost next (reflectedInput S.val)
    simpa only [expectedCost,reflected_input_oracle] using h

/-- The relative multiplicative formulation already fails on normalized
finite-step densities, for either prescribed extremal-root rule. -/
theorem relative_attempted_expectations_unbounded
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent,
      ENNReal.ofReal p ≤ μ (relativeSuccess rule next I.val α)) :
    (⨆ I : StepInput Agent, MixedAttemptedMain.expectedAttempts μ rule next I.val) = ∞ := by
  apply attempted_expectations_unbounded rule next base α 0 p hn hα hα hp hnext
  intro I
  simpa only [relative_success_eq rule next I.val α hα hα1] using hsuccess I

/-- Validation of raw finite-cut returns is query-free and preserves the
actual attempted-call cost. Malformed outputs count as failures. -/
theorem raw_attempted_expectations_unbounded
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent,
      ENNReal.ofReal p ≤ μ (MixedRawMain.success rule next I.val α ε)) :
    (⨆ I : StepInput Agent, MixedRawMain.expectedAttempts μ rule next I.val) = ∞ := by
  let next' := OutputPostprocess.normalized RawPartition.decode next
  have hm := OutputPostprocess.normalized_measurable
    RawPartition.decode RawPartition.decode_measurable next hnext
  have hs (I : StepInput Agent) :
      ENNReal.ofReal p ≤ μ (success rule next' I.val α ε) := by
    simpa only [next',MixedRawMain.normalized_success] using hsuccess I
  have h := attempted_expectations_unbounded rule next' base α ε p hn hα hε hp hm hs
  simpa only [MixedAttemptedMain.expectedAttempts,MixedRawMain.expectedAttempts,next',
    OutputPostprocess.attemptedCost_normalized] using h

theorem raw_relative_attempted_expectations_unbounded
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent,
      ENNReal.ofReal p ≤ μ (MixedRawMain.relativeSuccess rule next I.val α)) :
    (⨆ I : StepInput Agent, MixedRawMain.expectedAttempts μ rule next I.val) = ∞ := by
  apply raw_attempted_expectations_unbounded rule next base α 0 p hn hα hα hp hnext
  intro I
  simpa only [MixedRawMain.relative_success_eq rule next I.val α hα hα1] using hsuccess I

end EnvyFreeResearch.Full.MixedFiniteStepMain
