import EnvyFreeResearch.Full.UpperSnapshotIntegrationThreshold

/-! The concrete sample scale absorbs every candidate attempted in one
Snapshot trial, not merely the ultimately accepted candidate. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRepairParameters
variable {n k : ℕ}

theorem small_endpoints_fit (hk : 0 < k) (hkn : k ≤ n) :
    (16*k)*(k+2) ≤ UpperRepair.fine n := by
  have hs := active_scale n k hkn
  have hscale : (48:ℝ)*k ≤ scale n := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hsone : (1:ℝ) ≤ scale n := (by norm_num : (1:ℝ) ≤ 2^42).trans (scale_large n)
  have hlog := logarithm_positive (scale_large n)
  have hp : (scale n:ℝ)^2 ≤ (scale n:ℝ)^18 := pow_le_pow_right₀ hsone (by omega)
  have hmul : (scale n:ℝ)^18 ≤ (scale n:ℝ)^18*(logarithm (scale n):ℝ)^2 := by
    have hl : (1:ℝ) ≤ logarithm (scale n) := by exact_mod_cast hlog
    nlinarith [sq_nonneg ((logarithm (scale n):ℝ)-1),pow_nonneg (zero_le_one.trans hsone) 18]
  have hkreal : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hcomp : (16*(k:ℝ))*((k:ℝ)+2) ≤ (scale n:ℝ)^2 := by
    nlinarith [sq_nonneg ((scale n:ℝ)-48*k)]
  have hfin : (16*(k:ℝ))*((k:ℝ)+2) ≤ (UpperRepair.fine n:ℝ) := by
    change _ ≤ (samples (scale n) (logarithm (scale n)):ℝ)
    rw [samples_cast]
    exact hcomp.trans (hp.trans hmul)
  exact_mod_cast hfin
end EnvyFreeResearch.Full.UpperSnapshotProtocol
