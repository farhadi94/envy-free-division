import EnvyFreeResearch.Full.UpperShrinkCarveAssembly

/-! The final retained colors satisfy one-sided physical mass bounds.
Normalization is by each active observer's original mass. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperComponentAssembly UpperEndpointCache
variable {n r k : ℕ}

theorem assembled_bounds (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Fin k → Fin n) (pieces : Fin r → State n) (history : History n)
    (hpair : Pairwise (fun e f => Disjoint (domain (pieces e).cells) (domain (pieces f).cells)))
    (normal : Fin k → ℝ) (hnormal : ∀ i, 0 < normal i)
    (x : Fin r → Option (Fin k) → ℝ) (f delta : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hrow : ∀ e, ∑ c, x e c=1)
    (hmoment : ∀ i j, ∑ e, ((μ (active i)).real (domain (pieces e).cells) / normal i) * x e (some j)=f)
    (hloss : ∀ i, ∑ e ∈ UpperWholePayments.splitCells x,
      (μ (active i)).real (domain (pieces e).cells) / normal i ≤ delta)
    (i j : Fin k) :
    (f-delta)*normal i ≤ (μ (active i)).real (domain ((assembledCarve pieces history x).old j).cells) ∧
      (μ (active i)).real (domain ((assembledCarve pieces history x).old j).cells) ≤ f*normal i := by
  have hb := integral_moment_bounds
    (fun i e => (μ (active i)).real (domain (pieces e).cells) / normal i) x f delta
    (fun i e => div_nonneg measureReal_nonneg (hnormal i).le) hbox hrow hmoment hloss i j
  simp only [← Finset.sum_div] at hb
  rw [← selected_mass (μ (active i)) pieces history (UpperWholePayments.integralCells x j) hpair] at hb
  exact ⟨(le_div_iff₀ (hnormal i)).mp hb.1,(div_le_iff₀ (hnormal i)).mp hb.2⟩

theorem assembled_valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (origin : State n) (pieces : Fin r → State n) (history : History n)
    (hpieces : ∀ e, WellFormed μ (pieces e))
    (hpair : Pairwise (fun e f => Disjoint (domain (pieces e).cells) (domain (pieces f).cells)))
    (htruth : Truthful μ history) (hhistory : ∀ e, (pieces e).history ⊆ history)
    (hcover : (⋃ e, domain (pieces e).cells)=domain origin.cells)
    (hnormal : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (x : Fin r → Option (Fin k) → ℝ) (G tau : ℝ)
    (hbox : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1) (hrow : ∀ e, ∑ c, x e c=1)
    (hmoment : ∀ i j, ∑ e, ((μ (active i)).real (domain (pieces e).cells) /
      (μ (active i)).real (domain origin.cells)) * x e (some j)=UpperShrink.fraction k G)
    (hloss : ∀ i, ∑ e ∈ UpperWholePayments.splitCells x,
      (μ (active i)).real (domain (pieces e).cells) /
      (μ (active i)).real (domain origin.cells) ≤ UpperShrink.error tau G) :
    (assembledCarve pieces history x).Valid μ active origin G tau := by
  refine ⟨?_,?_,?_,?_,?_,fun _ => rfl,?_,?_⟩
  · intro j
    exact selected_wellFormed μ pieces history _ hpieces hpair htruth hhistory
  · exact selected_wellFormed μ pieces history _ hpieces hpair htruth hhistory
  · intro i j hij
    exact selected_disjoint pieces history hpair _ _ (UpperWholePayments.integral_disjoint x hbox hrow i j hij)
  · intro j
    exact selected_disjoint pieces history hpair _ _ (integral_dummy_disjoint x j)
  · exact (assembled_material pieces history x).trans hcover
  · intro i j
    exact (assembled_bounds μ active pieces history hpair _ hnormal x _ _ hbox hrow hmoment hloss i j).1
  · intro i j
    exact (assembled_bounds μ active pieces history hpair _ hnormal x _ _ hbox hrow hmoment hloss i j).2

end EnvyFreeResearch.Full.UpperShrinkCarve
