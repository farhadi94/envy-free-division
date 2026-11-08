import EnvyFreeResearch.Full.UpperShrinkCarveMomentFloating
import EnvyFreeResearch.Full.UpperShrinkCarveDecay
import EnvyFreeResearch.Full.UpperShrinkCarveInitial

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

theorem initial_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (origin : State n) (hd : DisjointComponents origin.cells) (f : ℝ) (j : Fin k) :
    moment μ (initial origin f).pieces j = μ.real (domain origin.cells)*f := by
  let p : Piece k := ⟨origin.cells,fun c => match c with
    | none => 1-(k:ℝ)*f
    | some _ => f⟩
  exact children_moment μ p origin hd j

theorem initial_split_bound (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Fin k → Fin n) (origin : State n) (f : ℝ) :
    SplitBound μ active (fun i => (μ (active i)).real (domain origin.cells)) (initial origin f).pieces := by
  intro p hp _ i
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  apply measureReal_mono
  · intro x hx
    change x ∈ domain [c] at hx
    simp only [domain,union_empty] at hx
    exact mem_domain.mpr ⟨c,hc,hx⟩
  · exact measure_ne_top _ _

end EnvyFreeResearch.Full.UpperShrinkCarve
