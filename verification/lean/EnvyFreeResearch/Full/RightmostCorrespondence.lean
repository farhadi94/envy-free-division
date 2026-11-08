import EnvyFreeResearch.Full.RightmostMain
import EnvyFreeResearch.Full.MixedCorrespondence

/-! The greatest-root construction is a theorem about the reflected
physical signed measures, with the paper's actual relative predicate. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostCorrespondence
open Set MeasureTheory OracleProtocol RightmostOracle RightmostExecution RightmostSuccess
open MixedDensity MixedFrontier MixedObstruction IntervalAllocation PhysicalReflection
open scoped ENNReal Classical

variable {Agent Ω : Type*}

theorem reflectedProfile_involution (P : IntervalOracle.Profile Agent) :
    reflectedProfile (reflectedProfile P) = P := by
  cases P with
  | mk F hc hz =>
    unfold reflectedProfile
    congr
    funext i x
    simp only [reflectedProfile, sub_self, sub_sub_cancel, hz]
    ring

theorem reflected_density_profile (rows : Agent → Row) :
    toProfile (fun i => reflectRow (rows i)) = reflectedProfile (toProfile rows) := by
  unfold toProfile reflectedProfile
  congr
  funext i x
  exact reflectRow_cumulative (rows i) x

/-- A greatest-root oracle indexed directly by its physical profile. -/
def greatestOracle (P : IntervalOracle.Profile Agent) : IntervalOracle.Query Agent → Option ℝ :=
  RightmostOracle.oracle (reflectedProfile P)

theorem greatestOracle_isLegal (P : IntervalOracle.Profile Agent) :
    IntervalOracle.IsLegalOracle P (greatestOracle P) := by
  have h := RightmostOracle.oracle_isLegal (reflectedProfile P)
  simpa only [reflectedProfile_involution, greatestOracle] using h

theorem greatestOracle_cut_last (P : IntervalOracle.Profile Agent) (i : Agent) (a b t r : ℝ)
    (h : greatestOracle P (.cut i a b t) = some r) :
    ExtremalRoots.LastRoot (P.cumulative i) a b t r := by
  have hr := RightmostOracle.oracle_cut_last (reflectedProfile P) i a b t r h
  simpa only [reflectedProfile_involution] using hr

theorem reflected_oracle (rows : Agent → Row) :
    greatestOracle (toProfile (fun i => reflectRow (rows i))) = RightmostOracle.oracle (toProfile rows) := by
  rw [reflected_density_profile]
  simp only [greatestOracle, reflectedProfile_involution]

theorem relative_iff_approximate [Fintype Agent] {α : ℝ}
    (S : State Agent α) (A : Allocation Agent) (hα : 0 < α) (hα1 : α ≤ 1) :
    MixedCorrespondence.RelativeEF (fun i => reflectRow (S.rows i)) A α ↔
      RightmostFailure.ApproximateEF S A 0 := by
  apply MixedApproximation.relative_iff_cake_comparisons
    (fun i j => value (reflectRow (S.rows i)) (A.share j)) α hα hα1
  intro i
  rw [MixedCorrespondence.sum_value_share]
  simp only [reflectRow_cumulative, sub_self, Row.cumulative_zero, sub_zero, (S.ceiling i).1]
  norm_num

def relativeSuccess
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) : Set Ω :=
  {ω | ∃ fuel A, (run next (RightmostOracle.oracle (profile S)) ω fuel []).stop = .returned A ∧
    MixedCorrespondence.RelativeEF (fun i => reflectRow (S.rows i)) A α}

theorem relativeSuccess_eq [Fintype Agent]
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    {α : ℝ} (S : State Agent α) (hα : 0 < α) (hα1 : α ≤ 1) :
    relativeSuccess next S = success next S 0 := by
  ext ω
  simp only [relativeSuccess, success, mem_ofPred_eq, mem_iUnion,
    RightmostAmplification.capSuccess, relative_iff_approximate S _ hα hα1]

theorem relative_expected_queries_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ}
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hruns : RightmostViews.MeasurableRuns (α := α) next)
    (p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hsuccess : ∀ S : State Agent α, ENNReal.ofReal p ≤ μ (relativeSuccess next S)) :
    (⨆ S : State Agent α,
      ∫⁻ ω, (queryCost next (RightmostOracle.oracle (profile S)) ω [] : ℝ≥0∞) ∂μ) = ∞ := by
  apply RightmostMain.expected_queries_unbounded_of_runs next base hruns 0 p hn hα hα hp
  intro S
  simpa only [relativeSuccess_eq next S hα hα1] using hsuccess S

end EnvyFreeResearch.Full.RightmostCorrespondence
