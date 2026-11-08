import EnvyFreeResearch.Full.UpperShrinkCarveProgram
import EnvyFreeResearch.Full.UpperShrinkMedianHalving

/-! Every child of an actually queried median pass has at most half of
its parent mass for every queried observer, including zero parent rows. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

theorem medianChain_domain (policy : Policy n) (cutters : List (Fin n)) (state : State n) :
    domain (medianChainExecute policy cutters state).cells = domain state.cells := by
  induction cutters generalizing state with
  | nil => rfl
  | cons i rest ih =>
    exact (ih (UpperShrink.median policy state i).2).trans (UpperShrink.median_domain policy state i)

theorem medianChain_preserves_mass_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (policy : Policy n) (cutters : List (Fin n)) (state : State n) (B : ℝ)
    (hb : ∀ c ∈ state.cells, μ.real c.carrier ≤ B) :
    ∀ c ∈ (medianChainExecute policy cutters state).cells, μ.real c.carrier ≤ B := by
  induction cutters generalizing state with
  | nil => exact hb
  | cons i rest ih =>
    exact ih (UpperShrink.median policy state i).2
      (UpperShrink.median_preserves_mass_bound μ policy state i B hb)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)

include hp in
theorem medianChain_wellFormed (cutters : List (Fin n)) (state : State n)
    (hs : WellFormed μ state) : WellFormed μ (medianChainExecute policy cutters state) := by
  induction cutters generalizing state with
  | nil => exact hs
  | cons i rest ih =>
    exact ih _ (UpperShrink.median_wellFormed μ policy hp state hs i)

include hp in
theorem medianChain_components_half (cutters : List (Fin n)) (state : State n)
    (hs : WellFormed μ state) (i : Fin n) (hi : i ∈ cutters)
    (c : Component) (hc : c ∈ (medianChainExecute policy cutters state).cells) :
    (μ i).real c.carrier ≤ (μ i).real (domain state.cells) / 2 := by
  induction cutters generalizing state with
  | nil => simp at hi
  | cons j rest ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact medianChain_preserves_mass_bound (μ i) policy rest (UpperShrink.median policy state i).2 _
        (UpperShrink.median_components_half μ policy hp state hs i) c hc
    · have hb := ih (UpperShrink.median policy state j).2
        (UpperShrink.median_wellFormed μ policy hp state hs j) hi hc
      simpa only [UpperShrink.median_domain] using hb

end EnvyFreeResearch.Full.UpperShrinkCarve
