import EnvyFreeResearch.Full.UpperGlobalProtocolTransferPath

/-! The combinatorial transfer alternative after the first successful shrink.
The second branch specifies exactly the edge used after a second shrink. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Transfer
open scoped Classical

variable {k : ℕ}

def Certificate (E : Fin k → Fin k → Prop) (d : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (tau : ℝ) : Prop :=
  ∃ alpha : Equiv.Perm (Fin k), ∃ b h, E b h ∧
    (∀ i, d i (alpha i) ≤ tau*rho i) ∧ 2*rho b ≤ d b (alpha h)

theorem transfer_or_bad_edge (E : Fin k → Fin k → Prop)
    (d : Fin k → Fin k → ℝ) (rho : Fin k → ℝ) (tau : ℝ) (a j : Fin k)
    (htau : 0 ≤ tau) (hrho : ∀ i, 0 < rho i) (hdiag : ∀ i, d i i=0)
    (hlarge : 2*rho a ≤ d a j)
    (hdichotomy : ∀ i, d i j ≤ tau*rho i ∨ 2*rho i ≤ d i j)
    (forward : SimplePath E a j) (backward : ∀ h, SimplePath E j h) :
    Certificate E d rho tau ∨ ∃ p q, E p q ∧ tau*rho p < d p q := by
  have hj : ¬2*rho j ≤ d j j := by rw [hdiag]; linarith [hrho j]
  obtain ⟨edge,hi,hh⟩ := forward.crossing (fun i => 2*rho i ≤ d i j) hlarge hj
  let b := forward.vertex edge.castSucc
  let h := forward.vertex edge.succ
  have hE : E b h := forward.edge edge
  have hsmall : d h j ≤ tau*rho h := (hdichotomy h).resolve_right hh
  let path := backward h
  by_cases hsteps : ∀ e : Fin path.length,
      d (path.vertex e.castSucc) (path.vertex e.succ) ≤ tau*rho (path.vertex e.castSucc)
  · refine Or.inl ⟨path.cycle,b,h,hE,?_,?_⟩
    · exact path.cycle_small d rho tau hdiag (fun i => mul_nonneg htau (hrho i).le) hsmall hsteps
    · rw [path.cycle_last]
      exact hi
  · push_neg at hsteps
    obtain ⟨e,he⟩ := hsteps
    exact Or.inr ⟨path.vertex e.castSucc,path.vertex e.succ,path.edge e,he⟩

theorem second_shrink_identity (E : Fin k → Fin k → Prop)
    (d : Fin k → Fin k → ℝ) (rho rho' : Fin k → ℝ) (tau : ℝ)
    (htau : 0 ≤ tau) (hrho' : ∀ i, 0 ≤ rho' i) (hdiag : ∀ i, d i i=0)
    (hshrink : ∀ i, rho' i ≤ tau*rho i/2)
    (p q : Fin k) (hE : E p q) (hbad : tau*rho p < d p q) :
    Certificate E d rho' tau := by
  refine ⟨Equiv.refl _,p,q,hE,?_,?_⟩
  · intro i
    simp only [Equiv.refl_apply,hdiag]
    exact mul_nonneg htau (hrho' i)
  · simp only [Equiv.refl_apply]
    linarith [hshrink p]

end EnvyFreeResearch.Full.UpperGlobal.Transfer
