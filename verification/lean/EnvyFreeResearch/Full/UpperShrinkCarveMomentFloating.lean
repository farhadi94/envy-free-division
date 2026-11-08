import EnvyFreeResearch.Full.UpperShrinkCarveMoments
import EnvyFreeResearch.Full.UpperShrinkCarvePhysical
import EnvyFreeResearch.Full.UpperShrinkCarveFractions

/-! The floating step preserves physical color moments because its queried
cache is truthful. Positive normalizers are used only to undo normalization. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

theorem cached_moment (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k)
    (hw : ∀ p ∈ mesh.pieces, WellFormed μ (⟨p.cells,mesh.history⟩ : State n)) (i j : Fin k) :
    (∑ e : Fin mesh.pieces.length, weights active normal mesh i e*(mesh.pieces.get e).fraction (some j)) =
      moment (μ (active i)) mesh.pieces j / normal i := by
  have hsum : (∑ e : Fin mesh.pieces.length,
      (μ (active i)).real (domain (mesh.pieces.get e).cells)*(mesh.pieces.get e).fraction (some j)) =
      moment (μ (active i)) mesh.pieces j := by
    rw [← moment_ofFn]
    simp only [List.ofFn_get]
  calc
    _ = (∑ e : Fin mesh.pieces.length,
      (μ (active i)).real (domain (mesh.pieces.get e).cells)*(mesh.pieces.get e).fraction (some j))/normal i := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      rw [weights,total_correct μ _ (hw _ (List.get_mem _ e))]
      ring
    _ = _ := by rw [hsum]

theorem floated_moment (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k)
    (hw : ∀ p ∈ mesh.pieces, WellFormed μ (⟨p.cells,mesh.history⟩ : State n))
    (hv : mesh.FractionsValid) (hn : ∀ i, normal i ≠ 0) (i j : Fin k) :
    moment (μ (active i)) (floated active normal mesh).pieces j = moment (μ (active i)) mesh.pieces j := by
  let x : UpperFloating.PaymentCoord (Fin k) (Fin mesh.pieces.length) → ℝ :=
    fun c => (mesh.pieces.get c.1).fraction c.2
  have hs := UpperFloating.select_spec (weights active normal mesh) x
    (fun c => (hv _ (List.get_mem _ c.1)).1 c.2)
    (fun e => (hv _ (List.get_mem _ e)).2)
  have hm := hs.2.2.1 i j
  have hnew : moment (μ (active i)) (floated active normal mesh).pieces j / normal i =
      ∑ e : Fin mesh.pieces.length, weights active normal mesh i e *
        UpperFloating.select (weights active normal mesh) x (e,some j) := by
    unfold floated
    rw [moment_ofFn,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    rw [weights,total_correct μ _ (hw _ (List.get_mem _ e))]
    ring
  apply (div_left_inj' (hn i)).mp
  rw [hnew,hm]
  exact cached_moment μ active normal mesh hw i j

end EnvyFreeResearch.Full.UpperShrinkCarve
