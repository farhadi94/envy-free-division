import EnvyFreeResearch.Full.RefinedUpperCorrectionChance

/-! Exceptional endpoints can be included in the analytic bad set without
paying for removed material: endpoint domination is restricted to the actual
retained domain. A finite grid-boundary set has zero mass for every row. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperEndpointExceptions

def augment {Index : Type*} (bad retained : Set ℝ) (grid : Index → ℝ) : Set ℝ :=
  (bad ∪ retainedᶜ) ∪ Set.range grid

theorem augment_measurable {Index : Type*} [Finite Index] (bad retained : Set ℝ) (grid : Index → ℝ)
    (hb : MeasurableSet bad) (ht : MeasurableSet retained) :
    MeasurableSet (augment bad retained grid) :=
  (hb.union ht.compl).union (Set.finite_range grid).measurableSet

theorem outside_augment {Index : Type*} (bad retained : Set ℝ) (grid : Index → ℝ)
    (x : ℝ) (hx : x ∉ augment bad retained grid) :
    x ∉ bad ∧ x ∈ retained ∧ x ∉ Set.range grid := by
  simpa only [augment, mem_union, not_or, mem_compl_iff, not_not, and_assoc] using hx

theorem restricted_bad_mass_le {Index : Type*} [Finite Index]
    (μ : Measure ℝ) [NullSingletonClass μ]
    (bad retained buffer : Set ℝ) (grid : Index → ℝ)
    (ht : MeasurableSet retained) (hsub : retained ⊆ buffer) :
    (μ.restrict retained) (augment bad retained grid) ≤ (μ.restrict buffer) bad := by
  have hc : (μ.restrict retained) retainedᶜ = 0 := by
    rw [Measure.restrict_apply ht.compl]
    simp
  have hg : (μ.restrict retained) (Set.range grid) = 0 :=
    (Set.finite_range grid).measure_zero _
  calc
    _ ≤ (μ.restrict retained) (bad ∪ retainedᶜ) + (μ.restrict retained) (Set.range grid) :=
      measure_union_le _ _
    _ ≤ ((μ.restrict retained) bad + (μ.restrict retained) retainedᶜ) +
        (μ.restrict retained) (Set.range grid) := add_le_add (measure_union_le _ _) le_rfl
    _ = (μ.restrict retained) bad := by rw [hc, hg]; simp
    _ ≤ _ := Measure.restrict_mono_set μ hsub bad

end EnvyFreeResearch.Full.RefinedUpperEndpointExceptions
