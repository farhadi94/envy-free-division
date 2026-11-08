import EnvyFreeResearch.Full.UpperGlobalProtocolTransferSelectionSearch

/-! Correctness of the concrete finite selector on the actual transfer
alternative, including the prescribed identity after a second shrink. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Transfer.Selection
open scoped Classical

variable {k : ℕ}

theorem exists_valid_of_alternative (tau : ℝ) (data : CachedData k)
    (h : Certificate (fun i j => data.1 i j=true) data.2.1 data.2.2 tau ∨
      ∃ p q, data.1 p q=true ∧ tau*data.2.2 p < data.2.1 p q) :
    ∃ c, Valid tau data c := by
  rcases h with ⟨alpha,b,h,hE,hown,hlarge⟩ | ⟨p,q,hE,hbad⟩
  · exact ⟨.commit alpha b h,hE,hown,hlarge⟩
  · exact ⟨.shrink p q,hE,hbad⟩

theorem select_of_alternative (tau : ℝ) (data : CachedData k)
    (h : Certificate (fun i j => data.1 i j=true) data.2.1 data.2.2 tau ∨
      ∃ p q, data.1 p q=true ∧ tau*data.2.2 p < data.2.1 p q) :
    ∃ c, select tau data=some c ∧ Valid tau data c :=
  select_correct tau data (exists_valid_of_alternative tau data h)

theorem commit_certificate (tau : ℝ) (data : CachedData k)
    (alpha : Equiv.Perm (Fin k)) (b h : Fin k)
    (hv : Valid tau data (.commit alpha b h)) :
    Certificate (fun i j => data.1 i j=true) data.2.1 data.2.2 tau :=
  ⟨alpha,b,h,hv⟩

theorem second_commit_valid (tau : ℝ) (data : CachedData k) (rho' : Fin k → ℝ)
    (p q : Fin k) (hv : Valid tau data (.shrink p q))
    (htau : 0 ≤ tau) (hrho' : ∀ i, 0 ≤ rho' i) (hdiag : ∀ i, data.2.1 i i=0)
    (hshrink : ∀ i, rho' i ≤ tau*data.2.2 i/2) :
    Valid tau (data.1,data.2.1,rho') (.commit (Equiv.refl _) p q) := by
  refine ⟨hv.1,?_,?_⟩
  · intro i
    simp only [Equiv.refl_apply,hdiag]
    exact mul_nonneg htau (hrho' i)
  · simp only [Equiv.refl_apply]
    have hbad := hv.2
    linarith [hshrink p]

/-- The explicit finite selector succeeds for every accepted first-shrink
output under the manuscript's concrete snapshot and connectivity premises. -/
theorem select_after_first_shrink (graph : Fin k → Fin k → Bool)
    (d : Fin k → Fin k → ℝ) (r : Fin k → ℝ) (theta tau : ℝ) (a j : Fin k)
    (htheta : 0 < theta) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hr : ∀ i, 0 < r i) (hd : ∀ i h, 0 ≤ d i h) (hdiag : ∀ i, d i i=0)
    (hcert : theta*r a ≤ d a j)
    (hreach : ∀ i h, Relation.ReflTransGen (fun p q => graph p q=true) i h)
    (rho : Fin k → ℝ) (hpos : ∀ i, 0 < rho i)
    (hlo : ∀ i, 3*r i/(8*factor theta tau
      (factorIndex theta tau (fun i => d i j/r i) j).val) ≤ rho i)
    (hup : ∀ i, rho i ≤ r i/factor theta tau
      (factorIndex theta tau (fun i => d i j/r i) j).val) :
    ∃ c, select tau (graph,d,rho)=some c ∧ Valid tau (graph,d,rho) c := by
  apply select_of_alternative
  exact selected_factor_transfer (fun i h => graph i h=true) d r theta tau a j
    htheta htau htau1 hr hd hdiag hcert hreach rho hpos hlo hup

end EnvyFreeResearch.Full.UpperGlobal.Transfer.Selection
