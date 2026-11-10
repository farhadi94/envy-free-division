import EnvyFreeResearch.Full.RefinedUpperParameterCounts
import EnvyFreeResearch.Full.UpperSnapshotCandidatesParameters
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters

/-! Numerical Snapshot guards at the revised sample count. The physical
contrast lemmas are unchanged; probability uses the fixed-measure endpoint
estimate with the actual new m. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotParameters
open RefinedUpperParameterCounts
open scoped ENNReal

def accuracy (s : ℕ) : ℝ := 1/(s:ℝ)^2
def margin (s ell : ℕ) : ℝ := oldError s/(768*samples s ell)

theorem coarse_cap_small {s ell : ℕ} (hs : 2 ≤ s) (he : 1 ≤ ell) :
    1/((coarseCount s ell:ℝ)+1) ≤ oldError s/2 ∧
      1/((coarseCount s ell:ℝ)+1) ≤ 1/4 := by
  have hsr : (2:ℝ) ≤ s := by exact_mod_cast hs
  have her : (1:ℝ) ≤ ell := by exact_mod_cast he
  have hp : (2:ℝ)^6 ≤ (s:ℝ)^6 := pow_le_pow_left₀ (by norm_num) hsr 6
  have hden : 8*(s:ℝ)^2 ≤ (s:ℝ)^8*ell := by
    have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (s:ℝ))
    have hmore := mul_le_mul_of_nonneg_left her (pow_nonneg (Nat.cast_nonneg s : (0:ℝ) ≤ s) 8)
    nlinarith [show (s:ℝ)^6*(s:ℝ)^2=(s:ℝ)^8 by ring]
  have hcap : 1/((coarseCount s ell:ℝ)+1) ≤ 1/(8*(s:ℝ)^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    rw [coarseCount_cast]
    linarith
  constructor
  · calc
      _ ≤ 1/(8*(s:ℝ)^2) := hcap
      _ = oldError s/2 := by unfold oldError; ring
  · have hsmall : 1/(8*(s:ℝ)^2) ≤ 1/4 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    exact hcap.trans hsmall

theorem snapshot_failure_small {s ell k : ℕ} (hd : 128 ∣ s)
    (hs : (4096:ℝ) ≤ s) (he : (1:ℝ) ≤ ell) (hk : (k:ℝ) ≤ s) :
    128*(k:ℝ)^5*(1+accuracy s)/(accuracy s*((samples s ell:ℝ)+1)) < 1/64 := by
  have hsp : (0:ℝ)<s := by linarith
  have hep : (0:ℝ)<ell := by linarith
  have hp : 0<accuracy s := by unfold accuracy; positivity
  have heps : accuracy s ≤ 1 := by
    unfold accuracy
    exact (div_le_one (by positivity : (0:ℝ)<(s:ℝ)^2)).mpr (by nlinarith)
  have hden : accuracy s*(samples s ell:ℝ)=(s:ℝ)^7*ell/128 := by
    rw [samples_cast hd, accuracy]
    field_simp
  have hfirst : 128*(k:ℝ)^5*(1+accuracy s)/(accuracy s*((samples s ell:ℝ)+1)) ≤
      32768*(k:ℝ)^5/((s:ℝ)^7*ell) := by
    calc
      _ ≤ (256*(k:ℝ)^5)/((s:ℝ)^7*ell/128) := by
        apply div_le_div₀
        · positivity
        · nlinarith [pow_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) 5]
        · positivity
        · rw [mul_add,hden]
          linarith
      _ = _ := by ring
  have hk5 := pow_le_pow_left₀ (Nat.cast_nonneg k : (0:ℝ) ≤ k) hk 5
  have hsecond : 32768*(k:ℝ)^5/((s:ℝ)^7*ell) ≤ 32768/(s:ℝ)^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hk5 (sq_nonneg (s:ℝ))
    have he' := mul_le_mul_of_nonneg_left he (pow_nonneg (hsp.le) 7)
    nlinarith [show (s:ℝ)^5*(s:ℝ)^2=(s:ℝ)^7 by ring]
  have hlast : 32768/(s:ℝ)^2 < 1/64 := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<(s:ℝ)^2)).mpr
    nlinarith
  exact hfirst.trans_lt (hsecond.trans_lt hlast)

theorem population_nearError {s k : ℕ} (hs : (1:ℝ) ≤ s) (hk : (k:ℝ) ≤ s) :
    (k:ℝ)*oldError s ≤ 2 := by
  unfold oldError
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(s:ℝ)^2)).mpr
  nlinarith

theorem large_margin (D tau M m : ℝ) (hD : tau/16 ≤ D) (htau : 0 ≤ tau)
    (hM : 0 < M) (hm : 0 < m) (hcount : M ≤ 2*m) :
    tau/(768*m) ≤ (D/(3*M))/8 :=
  UpperSnapshotCandidates.large_margin_scale D tau M m hD htau hM hm hcount

end EnvyFreeResearch.Full.RefinedUpperSnapshotParameters
