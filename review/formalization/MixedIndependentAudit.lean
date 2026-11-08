import EnvyFreeResearch.Full.MixedCorrespondence
import EnvyFreeResearch.Full.RightmostCorrespondence

/- Independent review audit. No construction module is modified here. -/

#print axioms EnvyFreeResearch.Full.MixedLeftmostMain.finite_horizon_hard_input
#print axioms EnvyFreeResearch.Full.MixedLeftmostMain.expected_queries_unbounded
#print axioms EnvyFreeResearch.Full.MixedCorrespondence.relative_expected_queries_unbounded
#print axioms EnvyFreeResearch.Full.RightmostMain.finite_horizon_hard_input
#print axioms EnvyFreeResearch.Full.RightmostMain.expected_queries_unbounded
#print axioms EnvyFreeResearch.Full.RightmostCorrespondence.relative_expected_queries_unbounded
#print axioms EnvyFreeResearch.Full.RightmostCorrespondence.greatestOracle_isLegal
#print axioms EnvyFreeResearch.Full.RightmostCorrespondence.greatestOracle_cut_last
#print axioms EnvyFreeResearch.Full.RightmostCorrespondence.reflected_density_profile
#print axioms EnvyFreeResearch.Full.MixedCorrespondence.value_Icc
#print axioms EnvyFreeResearch.Full.MixedCorrespondence.sum_value_share
#print axioms EnvyFreeResearch.Full.MixedCorrespondence.relative_iff_approximate
#print axioms EnvyFreeResearch.Full.MixedMeasurableOracle.boundedFirst_measurable
#print axioms EnvyFreeResearch.Full.MixedViews.concrete_measurable_views
#print axioms EnvyFreeResearch.Full.RightmostViews.concrete_measurable_views
#print axioms EnvyFreeResearch.Full.MixedSuccess.success_below_cap
#print axioms EnvyFreeResearch.Full.RightmostSuccess.success_below_cap

namespace MixedIndependentAudit
open EnvyFreeResearch.Full

-- The hard-state space is inhabited for the exact paper regime; the
-- conclusion cannot follow merely from an empty family of legal inputs.
example : Nonempty (MixedFrontier.State (Fin 3) (1 : ℝ)) :=
  ⟨MixedFrontier.initial (Fin 3) 1⟩

-- Normalize the whole physical interval, not just a scalar profile field.
example (α : ℝ) (S : MixedFrontier.State (Fin 3) α) (i : Fin 3) :
    MixedObstruction.value (S.rows i) (Set.Icc (0 : ℝ) 1) = 1 := by
  rw [MixedCorrespondence.value_Icc (S.rows i) (by norm_num) (by norm_num)
    (by norm_num), MixedDensity.Row.cumulative_zero, sub_zero]
  exact (S.ceiling i).1

end MixedIndependentAudit
