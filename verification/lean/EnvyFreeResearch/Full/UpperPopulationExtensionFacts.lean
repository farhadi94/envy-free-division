import EnvyFreeResearch.Full.UpperPopulationExtension

/-! All original observers and active comparisons survive the concrete
finite-population embedding and zero extension. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperCircularStage
variable {n : ℕ}

theorem extendPermutation_symm_apply (active : Finset (Fin n))
    (f : Equiv.Perm (Fin active.card)) (i : Fin active.card) :
    (extendPermutation active f).symm (enumerate active i) = enumerate active (f.symm i) := by
  apply (extendPermutation active f).injective
  rw [Equiv.apply_symm_apply,extendPermutation_apply,Equiv.apply_symm_apply]

theorem extendPieces_frozen_value (μ : Fin n → Measure ℝ) (active : Finset (Fin n))
    (pieces : Fin active.card → State n) (history : History n) (i j : Fin n) (hj : j ∉ active) :
    (μ i).real (domain (extendPieces active pieces history j).cells) = 0 := by
  rw [extendPieces_frozen _ _ _ _ hj]
  exact measureReal_empty

theorem extendPieces_activeEF (μ : Fin n → Measure ℝ) (direction : GlobalCompletion.Direction)
    (active : Finset (Fin n)) (pieces : Fin active.card → State n) (history : History n)
    (hEF : GlobalCompletion.EnvyFree direction
      (fun i j => (μ (enumerate active i)).real (domain (pieces j).cells))) :
    GlobalCompletion.ActiveEF direction
      (fun i j => (μ i).real (domain (extendPieces active pieces history j).cells)) (↑active) := by
  intro i hi j hj
  obtain ⟨a,rfl⟩ := enumerate_preimage active i hi
  obtain ⟨b,rfl⟩ := enumerate_preimage active j hj
  have h := hEF a b
  cases direction <;>
    simpa only [GlobalCompletion.margin,extendPieces_apply] using h

end EnvyFreeResearch.Full.UpperZeroRows
