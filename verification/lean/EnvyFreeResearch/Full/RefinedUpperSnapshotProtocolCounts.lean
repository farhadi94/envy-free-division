import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLaw

/-! Revised sample count absorbs every attempted two-circle candidate. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale)

theorem small_endpoints_fit {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (16*k)*(k+2) ≤ RefinedUpperRepair.fine n := by
  have hs : 256 ≤ scale n := by
    exact_mod_cast (show (256:ℝ) ≤ scale n from (by norm_num : (256:ℝ) ≤ 2^42).trans (scale_large n))
  have he := logarithm_positive (scale_large n)
  have ha : 256*k ≤ scale n := by
    have h := active_scale n k hkn
    exact_mod_cast (show (256:ℝ)*k ≤ scale n by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  exact RefinedUpperParameterCounts.candidate_queries_fit hs he ha hk
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
