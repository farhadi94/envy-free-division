import EnvyFreeResearch.Full.UpperShrinkMedianFacts

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridRecords
  UpperCircularStage

theorem separated_component_half (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : List Component) (x : ℝ) (hsep : SeparatedAt x cells)
    (hhalf : μ.real (domain cells ∩ Iic x) = μ.real (domain cells) / 2)
    (c : Component) (hc : c ∈ cells) : μ.real c.carrier ≤ μ.real (domain cells) / 2 := by
  have hsub : c.carrier ⊆ domain cells := fun _ hx => mem_domain.mpr ⟨c, hc, hx⟩
  by_cases hr : c.right ≤ x
  · rw [← hhalf]
    exact measureReal_mono (fun y hy => ⟨hsub hy, (c.subset_closed hy).2.trans hr⟩)
  · have hs : c.carrier ⊆ domain cells \ (domain cells ∩ Iic x) := by
      intro y hy
      exact ⟨hsub hy, fun hh => not_le_of_gt (show x < y from hsep c hc (lt_of_not_ge hr) hy) (show y ≤ x from hh.2)⟩
    have hb := measureReal_mono (μ := μ) hs
    rw [measureReal_sdiff inter_subset_left ((domain_measurable cells).inter measurableSet_Iic), hhalf] at hb
    linarith

theorem refineEndpoints_preserves_separated (cells : List Component) (points : List ℝ) (x : ℝ)
    (hs : SeparatedAt x cells) : SeparatedAt x (refineEndpoints cells points) := by
  induction points generalizing cells with
  | nil => exact hs
  | cons p points ih => exact ih _ (refineAt_preserves_separated p x cells hs)

theorem refineEndpoints_preserves_mass_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : List Component) (points : List ℝ) (B : ℝ)
    (hb : ∀ c ∈ cells, μ.real c.carrier ≤ B) :
    ∀ c ∈ refineEndpoints cells points, μ.real c.carrier ≤ B := by
  induction points generalizing cells with
  | nil => exact hb
  | cons p points ih =>
    apply ih
    intro c hc
    obtain ⟨parent, hparent, hchild⟩ := List.mem_flatMap.mp hc
    exact (measureReal_mono (splitAt_subpart p parent c hchild).1).trans (hb parent hparent)

theorem median_preserves_mass_bound {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (policy : Policy n) (state : State n) (cutter : Fin n) (B : ℝ)
    (hb : ∀ c ∈ state.cells, μ.real c.carrier ≤ B) :
    ∀ c ∈ (median policy state cutter).2.cells, μ.real c.carrier ≤ B := by
  unfold median
  split_ifs
  · exact hb
  · exact refineEndpoints_preserves_mass_bound μ _ _ B hb

variable {n : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
  (state : State n) (hs : WellFormed μ state) (cutter : Fin n)

include hp hs in
theorem median_components_half (c : Component) (hc : c ∈ (median policy state cutter).2.cells) :
    (μ cutter).real c.carrier ≤ (μ cutter).real (domain state.cells) / 2 := by
  by_cases hz : (μ cutter).real (domain state.cells) = 0
  · rw [median_zero μ policy state hs cutter hz] at hc
    have hb := measureReal_mono (μ := μ cutter)
      (show c.carrier ⊆ domain state.cells from fun _ hx => mem_domain.mpr ⟨c, hc, hx⟩)
    rw [hz] at hb ⊢
    simpa using hb
  · have hpos := lt_of_le_of_ne (measureReal_nonneg (μ := μ cutter) (s := domain state.cells)) (fun he => hz he.symm)
    obtain ⟨x, hx, _, hh⟩ := median_positive_endpoint μ policy hp state hs cutter hpos
    have hsep : SeparatedAt x (median policy state cutter).2.cells := by
      have hn : ¬total state cutter ≤ 0 := by
        rw [total_correct μ state hs cutter]
        exact not_le_of_gt hpos
      simp only [median, hn, ite_false, Option.some.injEq] at hx ⊢
      subst x
      exact refineAt_separated _ _
    have hhalf : (μ cutter).real (domain (median policy state cutter).2.cells ∩ Iic x) =
        (μ cutter).real (domain (median policy state cutter).2.cells) / 2 := by
      simpa only [median_domain] using hh
    have hb := separated_component_half (μ cutter) _ x hsep hhalf c hc
    simpa only [median_domain] using hb

end EnvyFreeResearch.Full.UpperShrink
