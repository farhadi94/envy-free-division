import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferSelection
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferChoice

namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer

/-- The guarantee holds for the explicit Borel first-safe selector. -/
theorem selected_factor_transfer {k : ℕ} (E : Fin k → Fin k → Prop)
    (d : Fin k → Fin k → ℝ) (r : Fin k → ℝ) (theta tau : ℝ) (a j : Fin k)
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hr : ∀ i, 0 < r i) (hd : ∀ i h, 0 ≤ d i h) (hdiag : ∀ i, d i i=0)
    (hcert : theta*r a ≤ d a j)
    (hreach : ∀ i h, Relation.ReflTransGen E i h)
    (rho : Fin k → ℝ) (hpos : ∀ i, 0 < rho i)
    (hlo : ∀ i, 3*r i/(8*factor theta tau
      (factorIndex theta tau (fun i => d i j/r i) j).val) ≤ rho i)
    (hup : ∀ i, rho i ≤ r i/factor theta tau
      (factorIndex theta tau (fun i => d i j/r i) j).val) :
    Certificate E d rho tau ∨ ∃ p q, E p q ∧ tau*rho p < d p q := by
  let e := factorIndex theta tau (fun i => d i j/r i) j
  have he := factorIndex_safe theta tau (fun i => d i j/r i) j htheta htau htau1
    (fun i => div_nonneg (hd i j) (hr i).le) (by rw [hdiag,zero_div])
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
