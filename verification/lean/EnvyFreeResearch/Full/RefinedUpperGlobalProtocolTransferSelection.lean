import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransfer
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferShrink
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferReachability

/-! Actual finite first-factor choice and its uniform guarantee for every
successful Shrink output. The only path premise is directed reachability. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
open scoped Classical

/-- The finite choice precedes the Shrink call; hence it works for every
accepted output satisfying that prescribed call's residue inequalities. -/
theorem first_factor_transfer {k : ℕ} (E : Fin k → Fin k → Prop)
    (d : Fin k → Fin k → ℝ) (r : Fin k → ℝ) (theta tau : ℝ) (a j : Fin k)
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hr : ∀ i, 0 < r i) (hd : ∀ i h, 0 ≤ d i h) (hdiag : ∀ i, d i i=0)
    (hcert : theta*r a ≤ d a j)
    (hreach : ∀ i h, Relation.ReflTransGen E i h) :
    ∃ e : Fin k, ∀ rho : Fin k → ℝ,
      (∀ i, 0 < rho i) →
      (∀ i, 3*r i/(8*factor theta tau e.val) ≤ rho i) →
      (∀ i, rho i ≤ r i/factor theta tau e.val) →
      Certificate E d rho tau ∨ ∃ p q, E p q ∧ tau*rho p < d p q := by
  obtain ⟨e,he⟩ := geometric_safe_factor theta tau (fun i => d i j/r i) j
    htheta htau htau1 (fun i => div_nonneg (hd i j) (hr i).le) (by rw [hdiag,zero_div])
  refine ⟨e,fun rho hpos hlo hup => ?_⟩
  have hG := factor_pos htheta htau e.val
  have hdi i := shrink_dichotomy (hr i) hG htau.le (hlo i) (hup i) (he i)
  have hscaled : theta ≤ d a j/r a := (le_div_iff₀ (hr a)).mpr hcert
  have hlarge : 2*rho a ≤ d a j := by
    have hh := certificate_row_large htheta htau htau1 hscaled e.val
    have hh' : 2*r a ≤ factor theta tau e.val*d a j :=
      (le_div_iff₀ (hr a)).mp (by simpa only [mul_div_assoc] using hh)
    have hu := (le_div_iff₀ hG).mp (hup a)
    nlinarith
  exact transfer_or_bad_edge E d rho tau a j htau.le hpos hdiag hlarge hdi
    (SimplePath.ofReachable (hreach a j)) (fun h => SimplePath.ofReachable (hreach j h))

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer
