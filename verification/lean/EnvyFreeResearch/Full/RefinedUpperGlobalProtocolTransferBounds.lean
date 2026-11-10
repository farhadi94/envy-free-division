import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferPath
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferShrink

namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer

theorem SimplePath.length_lt {k : ℕ} {E : Fin k → Fin k → Prop} {a b : Fin k}
    (path : SimplePath E a b) : path.length < k := by
  have h := Fintype.card_le_of_injective path.vertex path.injective
  simpa only [Fintype.card_fin,Nat.add_one_le_iff] using h

theorem factor_mono {theta tau : ℝ} (htheta : 0 < theta) (htau : 0 < tau)
    (htau1 : tau ≤ 1) : Monotone (factor theta tau) := by
  intro e f hef
  have hb : 1 ≤ 8/tau := (le_div_iff₀ htau).mpr (by linarith)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hef) (by positivity)

theorem factor_at_most_last {k : ℕ} (e : Fin k) {theta tau : ℝ}
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1) :
    factor theta tau e.val ≤ factor theta tau (k-1) :=
  factor_mono htheta htau htau1 (by omega)

theorem second_factor_at_most_last {k : ℕ} (hk : 2 ≤ k) {theta tau : ℝ}
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1) :
    2/tau ≤ factor theta tau (k-1) := by
  have hsmall : 2/tau ≤ factor theta tau 1 := by
    unfold factor
    rw [pow_one]
    have hs : 1 ≤ 2/theta := (le_div_iff₀ htheta).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 8/tau by positivity)
    have hd : 2/tau ≤ 8/tau := div_le_div_of_nonneg_right (by norm_num) htau.le
    nlinarith
  exact hsmall.trans (factor_mono htheta htau htau1 (by omega))

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
