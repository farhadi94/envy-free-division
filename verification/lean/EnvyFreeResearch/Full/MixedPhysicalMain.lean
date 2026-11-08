import EnvyFreeResearch.Full.RightmostCorrespondence

/-!
The mixed lower bound stated directly for normalized physical inputs and
the two prescribed root rules. The adversary's internal State does not
occur in the public success guarantee or the input class.
-/

noncomputable section
namespace EnvyFreeResearch.Full.MixedPhysicalMain
open Set MeasureTheory OracleProtocol MixedDensity MixedObstruction IntervalAllocation
open PhysicalReflection
open scoped ENNReal Classical

variable {Agent Ω : Type*}

structure Input (Agent : Type*) where
  rows : Agent → Row
  normalized : ∀ i, (rows i).cumulative 1 = 1

inductive RootRule | leftmost | rightmost

def oracle (rule : RootRule) (I : Input Agent) : IntervalOracle.Query Agent → Option ℝ :=
  match rule with
  | .leftmost => IntervalOracle.oracle (toProfile I.rows)
  | .rightmost => RightmostCorrespondence.greatestOracle (toProfile I.rows)

theorem oracle_isLegal (rule : RootRule) (I : Input Agent) :
    IntervalOracle.IsLegalOracle (toProfile I.rows) (oracle rule I) := by
  cases rule with
  | leftmost => exact IntervalOracle.oracle_isLegal _
  | rightmost => exact RightmostCorrespondence.greatestOracle_isLegal _

def Fair (I : Input Agent) (A : Allocation Agent) (α ε : ℝ) : Prop :=
  ∀ i j, α * value (I.rows i) (A.share j) - value (I.rows i) (A.share i) ≤ ε

def success (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (I : Input Agent) (α ε : ℝ) : Set Ω :=
  {ω | ∃ fuel A, (run next (oracle rule I) ω fuel []).stop = .returned A ∧ Fair I A α ε}

def expectedCost [MeasurableSpace Ω] (μ : Measure Ω) (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (I : Input Agent) : ℝ≥0∞ :=
  ∫⁻ ω, (queryCost next (oracle rule I) ω [] : ℝ≥0∞) ∂μ

def stateInput {α : ℝ} (S : MixedFrontier.State Agent α) : Input Agent :=
  ⟨S.rows, fun i => (S.ceiling i).1⟩

def reflectedInput {α : ℝ} (S : MixedFrontier.State Agent α) : Input Agent where
  rows i := reflectRow (S.rows i)
  normalized i := by simp only [reflectRow_cumulative, sub_self, Row.cumulative_zero,
    sub_zero, (S.ceiling i).1]

theorem reflected_input_oracle {α : ℝ} (S : MixedFrontier.State Agent α) :
    oracle .rightmost (reflectedInput S) = RightmostOracle.oracle (RightmostExecution.profile S) :=
  RightmostCorrespondence.reflected_oracle S.rows

theorem left_success_eq {α : ℝ}
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (S : MixedFrontier.State Agent α) (ε : ℝ) :
    success .leftmost next (stateInput S) α ε = MixedSuccess.success next S ε := by
  ext ω
  simp only [success, MixedSuccess.success, MixedAmplification.capSuccess,
    mem_ofPred_eq, mem_iUnion, oracle, stateInput, MixedExecution.profile,
    Fair, MixedPhysicalFailure.ApproximateEF]

theorem right_success_eq {α : ℝ}
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (S : MixedFrontier.State Agent α) (ε : ℝ) :
    success .rightmost next (reflectedInput S) α ε = RightmostSuccess.success next S ε := by
  unfold success
  rw [reflected_input_oracle]
  ext ω
  simp only [RightmostSuccess.success,
    RightmostAmplification.capSuccess, mem_ofPred_eq, mem_iUnion,
    Fair, reflectedInput, RightmostFailure.ApproximateEF]

/-- On actual normalized finite atomless signed densities, no prescribed
extremal-root rule admits a uniform finite expected query bound. The only
protocol regularity assumption is measurability of each fixed-input run. -/
theorem expected_queries_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hruns : ∀ I : Input Agent, ∀ fuel,
      Measurable (fun ω => run next (oracle rule I) ω fuel []))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (success rule next I α ε)) :
    (⨆ I : Input Agent, expectedCost μ rule next I) = ∞ := by
  cases rule with
  | leftmost =>
    have hm : MixedViews.MeasurableRuns (α := α) next := fun S fuel => hruns (stateInput S) fuel
    have hs (S : MixedFrontier.State Agent α) :
        ENNReal.ofReal p ≤ μ (MixedSuccess.success next S ε) := by
      simpa only [left_success_eq] using hsuccess (stateInput S)
    have htop := MixedLeftmostMain.expected_queries_unbounded_of_runs
      next base hm ε p hn hα hε hp hs
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro S
    exact le_iSup_of_le (stateInput S) le_rfl
  | rightmost =>
    have hm : RightmostViews.MeasurableRuns (α := α) next := by
      intro S fuel
      simpa only [reflected_input_oracle] using hruns (reflectedInput S) fuel
    have hs (S : MixedFrontier.State Agent α) :
        ENNReal.ofReal p ≤ μ (RightmostSuccess.success next S ε) := by
      simpa only [right_success_eq] using hsuccess (reflectedInput S)
    have htop := RightmostMain.expected_queries_unbounded_of_runs
      next base hm ε p hn hα hε hp hs
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro S
    apply le_iSup_of_le (reflectedInput S)
    simp only [expectedCost, reflected_input_oracle, le_refl]

def relativeSuccess (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (I : Input Agent) (α : ℝ) : Set Ω :=
  {ω | ∃ fuel A, (run next (oracle rule I) ω fuel []).stop = .returned A ∧
    MixedCorrespondence.RelativeEF I.rows A α}

theorem relative_iff_fair [Fintype Agent] (I : Input Agent) (A : Allocation Agent)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MixedCorrespondence.RelativeEF I.rows A α ↔ Fair I A α 0 := by
  apply MixedApproximation.relative_iff_cake_comparisons
    (fun i j => value (I.rows i) (A.share j)) α hα hα1
  intro i
  rw [MixedCorrespondence.sum_value_share, I.normalized i]
  norm_num

theorem relative_success_eq [Fintype Agent] (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (I : Input Agent) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    relativeSuccess rule next I α = success rule next I α 0 := by
  ext ω
  simp only [relativeSuccess, success, mem_ofPred_eq, relative_iff_fair I _ α hα hα1]

/-- The multiplicative claim of the main mixed theorem, for each prescribed
root rule and every fixed positive success probability. -/
theorem relative_expected_queries_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hruns : ∀ I : Input Agent, ∀ fuel,
      Measurable (fun ω => run next (oracle rule I) ω fuel []))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (relativeSuccess rule next I α)) :
    (⨆ I : Input Agent, expectedCost μ rule next I) = ∞ := by
  apply expected_queries_unbounded rule next base α 0 p hn hα hα hp hruns
  intro I
  simpa only [relative_success_eq rule next I α hα hα1] using hsuccess I

end EnvyFreeResearch.Full.MixedPhysicalMain
