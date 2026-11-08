import EnvyFreeResearch.Full.UpperSnapshotProtocolCounts
import EnvyFreeResearch.Full.UpperSnapshotProtocolActual

/-! Scalar checks for the actual small-disagreement branch. These supply
the concrete candidate geometry and Near budgets before fresh Repair. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol

theorem small_amount_checks (tau D agents : ℝ) (htau : 0 < tau) (hD : 0 < D)
    (hsmall : D < tau/16) (hk : 2 ≤ agents) :
    let t := (1-(8/tau)*D)/agents
    0 < t ∧ t ≤ 1/2 ∧ t < 1 ∧ agents*t < 1 ∧ 1/(2*agents) ≤ t ∧
      1-agents*t = (8/tau)*D := by
  have hkp : 0 < agents := by linarith
  have hK : 0 < 8/tau := div_pos (by norm_num) htau
  have hKD : (8/tau)*D < 1/2 := by
    have h : (8*D)/tau < 1/2 := (div_lt_iff₀ htau).mpr (by linarith)
    convert h using 1 <;> ring
  have hid : agents*((1-(8/tau)*D)/agents) = 1-(8/tau)*D := by field_simp
  have htlower : 1/(2*agents) ≤ (1-(8/tau)*D)/agents := by
    apply (le_div_iff₀ hkp).mpr
    have heq : 1/(2*agents)*agents = 1/2 := by field_simp
    rw [heq]
    linarith
  refine ⟨div_pos (by linarith) hkp,?_,?_,?_,htlower,by rw [hid]; ring⟩
  · apply (div_le_iff₀ hkp).mpr
    nlinarith [mul_pos hK hD]
  · apply (div_lt_one hkp).mpr
    nlinarith [mul_pos hK hD]
  · rw [hid]
    linarith [mul_pos hK hD]

theorem small_error_budgets (tau D delta eps : ℝ) (htau : 0 < tau) (htau4 : tau ≤ 4)
    (hD : 0 ≤ D) (hd : 0 ≤ delta) (hdelta : delta ≤ D) (heps : eps ≤ 1/2) :
    (1/2+eps)*delta ≤ ((8/tau)*D)/2 ∧
    2*((1/2+eps)*delta) ≤ tau*(((8/tau)*D)/2) := by
  have he : (1/2+eps)*delta ≤ D := by nlinarith
  have hK : 2 ≤ 8/tau := (le_div_iff₀ htau).mpr (by linarith)
  have hid : tau*(((8/tau)*D)/2) = 4*D := by field_simp; ring
  constructor
  · nlinarith
  · rw [hid]
    linarith

theorem small_margin_scale (tau D agents samples : ℝ) (htau : 0 < tau) (htau4 : tau ≤ 4)
    (hD : 0 < D) (hk : 0 < agents) (hm : 8*agents ≤ samples) :
    tau/(768*samples) ≤ ((2*(D/(32*agents))/(3*((8/tau+2)*D)))/8) := by
  have hmp : 0 < samples := (mul_pos (by norm_num) hk).trans_le hm
  have heq : ((2*(D/(32*agents))/(3*((8/tau+2)*D)))/8) = tau/(384*agents*(8+2*tau)) := by
    field_simp
    <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_left htau.le (by positivity)
  nlinarith [mul_nonneg hk.le (sub_nonneg.mpr htau4)]
end EnvyFreeResearch.Full.UpperSnapshotProtocol
