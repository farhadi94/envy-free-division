import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolUnitRun
import EnvyFreeResearch.Full.RefinedUpperExpectedRuntimeActualPaid
import EnvyFreeResearch.Full.RefinedUpperGlobalRunCostMean
import EnvyFreeResearch.Full.RefinedUpperGlobalQueryEnvelopes

/-! Public end-to-end randomized exact cake/chore division on the closed unit
interval. The query total includes the actual initialization and every rejected
attempt. All physical, legal-oracle, probabilistic and termination premises of
the internal phases are discharged by the concrete execution. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperStageMeasurable IntervalOracle
variable {n : ℕ}

def unitQueries (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) : ℝ≥0∞ :=
  (2*n : ℕ) + totalQueries policy fallback chores (unitInitial policy) omega

def unitCuts (policy : Policy n) (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) : ℝ≥0∞ :=
  totalCuts policy fallback chores (unitInitial policy) omega

def UnitOutputCorrect (μ : Fin n → Measure ℝ) (policy : Policy n) (fallback : Fin n)
    (chores : Bool) (omega : Stream (Universal n)) : Prop :=
  ∃ t a, Phase.run policy fallback chores (unitInitial policy) t omega=.done a ∧
    Pairwise (fun i j => Disjoint (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) i)
      (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)) ∧
    (⋃j, RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)=Icc 0 1 ∧
    GlobalCompletion.EnvyFree (if chores then .chore else .cake)
      (fun i j => (μ i).real (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j))

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (oracle : AdaptiveOracle.Policy (Query n) ℝ)
  (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
  (hmeas : MeasurablePolicy (AdaptiveOracle.answer oracle)) (fallback : Fin n) (chores : Bool)
include horacle hmeas

theorem unit_output_almost_sure :
    ∀ᵐ omega ∂streamLaw (universalLaw n),
      UnitOutputCorrect μ (AdaptiveOracle.answer oracle) fallback chores omega := by
  have hp := UpperQueryLegality.answer_admissible _ oracle horacle
  have hi := unitInitial_valid μ (AdaptiveOracle.answer oracle) hp fallback chores
  have ht := actual_terminates μ (Icc 0 1) chores (RefinedUpperGlobalUnit.execute (AdaptiveOracle.answer oracle))
    hi (AdaptiveOracle.answer oracle) hp hmeas fallback
  filter_upwards [ht] with omega homega
  change ∃ t, (Phase.run (AdaptiveOracle.answer oracle) fallback chores
    (unitInitial (AdaptiveOracle.answer oracle)) t omega).finished=true at homega
  obtain ⟨t,ht⟩ := homega
  cases he : Phase.run (AdaptiveOracle.answer oracle) fallback chores
      (unitInitial (AdaptiveOracle.answer oracle)) t omega <;>
    try { rw [he] at ht; cases ht }
  case done a =>
    exact ⟨t,a,he,unitRun_done_output μ (AdaptiveOracle.answer oracle) hp fallback chores omega t a he⟩

theorem unit_expected_query_cut_bounds :
    (∫⁻ omega, unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      (100*n^3*RefinedUpperRepair.fine n : ℕ) ∧
    (∫⁻ omega, unitCuts (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      (49*n^2*RefinedUpperRepair.fine n : ℕ) := by
  have hp := UpperQueryLegality.answer_admissible _ oracle horacle
  have hi := unitInitial_valid μ (AdaptiveOracle.answer oracle) hp fallback chores
  have hm := actual_paid_mean μ (Icc 0 1) chores (RefinedUpperGlobalUnit.execute (AdaptiveOracle.answer oracle))
    hi (AdaptiveOracle.answer oracle) hp hmeas fallback
  have hc := expected_actual_costs μ (Icc 0 1) chores (RefinedUpperGlobalUnit.execute (AdaptiveOracle.answer oracle))
    hi oracle horacle fallback (streamLaw (universalLaw n))
    (actual_paidCount_measurable (AdaptiveOracle.answer oracle) hmeas fallback chores _)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hm)
  have hn : 1 ≤ n := by have := fallback.isLt; omega
  have hnat : 1 ≤ RefinedUpperRepair.fine n := RefinedUpperGlobalBounds.fine_positive n
  have hq := RefinedUpperGlobalBounds.query_ledger n (RefinedUpperRepair.fine n) hn (by omega)
  have hcut := RefinedUpperGlobalBounds.cut_ledger n (RefinedUpperRepair.fine n) hn (by omega)
  constructor
  · calc
      _ = (∫⁻ omega, totalQueries (AdaptiveOracle.answer oracle) fallback chores
          (unitInitial (AdaptiveOracle.answer oracle)) omega ∂streamLaw (universalLaw n)) + (2*n : ℕ) := by
        simp only [unitQueries]
        rw [lintegral_add_left measurable_const _]
        simp [add_comm]
      _ ≤ (96*n*n*(n-1)*RefinedUpperRepair.fine n+(n+1)*(n*(n-1)+1) : ℕ)+(2*n : ℕ) :=
        add_le_add hc.1 le_rfl
      _ ≤ _ := by
        have hq' : 96*n*n*(n-1)*RefinedUpperRepair.fine n+(n+1)*(n*(n-1)+1)+2*n ≤
            100*n^3*RefinedUpperRepair.fine n := by simpa only [Nat.mul_comm (n+1)] using hq
        exact_mod_cast hq'
  · exact hc.2.trans (by exact_mod_cast hcut)

theorem randomized_exact_envy_free :
    (∀ᵐ omega ∂streamLaw (universalLaw n),
      UnitOutputCorrect μ (AdaptiveOracle.answer oracle) fallback chores omega) ∧
    (∫⁻ omega, unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      (100*n^3*RefinedUpperRepair.fine n : ℕ) ∧
    (∫⁻ omega, unitCuts (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      (49*n^2*RefinedUpperRepair.fine n : ℕ) :=
  ⟨unit_output_almost_sure μ oracle horacle hmeas fallback chores,
    unit_expected_query_cut_bounds μ oracle horacle hmeas fallback chores⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
