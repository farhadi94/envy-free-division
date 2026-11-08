import EnvyFreeResearch.Full.UpperUnionMeasurable

/-!
# Physical circular sampling on a recorded finite union

Both boundaries are produced by the ordinary component-cut implementation.
The second call observes the first call and all its endpoint recordings.
The returned object is a literal subset of the original recorded domain.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperUnionCircular

open UpperCircular UpperPhysical UpperCircularStage UpperRecordedDomain UpperUnionSampling
  UpperStageMeasurable UpperUnionMeasurable Chores

abbrev Circle := UpperCircular.Circle

variable {n : ℕ}

def firstRun (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (start : Circle) : ℝ × History n :=
  sampleExecution policy history cutter cached total cells (value start)

def secondRun (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I)
    (start : Circle) : ℝ × History n :=
  sampleExecution policy (firstRun policy history cutter cached total cells start).2
    cutter cached total cells (value (start + project amount))

def piece (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I)
    (start : Circle) : Set ℝ :=
  physicalPiece (domain cells) amount start
    (firstRun policy history cutter cached total cells start).1
    (secondRun policy history cutter cached total cells amount start).1

theorem firstRun_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cells : List Component) : Measurable (firstRun policy history cutter cached total cells) :=
  (sampleExecution_measurable policy hpolicy history cutter cached total cells).comp measurable_value

theorem secondRun_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cells : List Component) (amount : I) :
    Measurable (secondRun policy history cutter cached total cells amount) :=
  sampleExecution_family_measurable policy hpolicy _
    (measurable_snd.comp (firstRun_measurable policy hpolicy history cutter cached total cells))
    cutter cached total cells _ (measurable_value.comp (measurable_id.add_const _))

theorem piece_partition (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) (start : Circle) :
    Disjoint (piece policy history cutter cached total cells amount start)
      (domain cells \ piece policy history cutter cached total cells amount start) ∧
    piece policy history cutter cached total cells amount start ∪
      (domain cells \ piece policy history cutter cached total cells amount start) = domain cells := by
  have hsub : piece policy history cutter cached total cells amount start ⊆ domain cells :=
    physicalPiece_subset _ _ _ _ _
  exact ⟨disjoint_sdiff_self_right, union_sdiff_cancel hsub⟩

theorem stage_query_bound (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) (start : Circle) :
    (secondRun policy history cutter cached total cells amount start).2.length ≤
      history.length + 2 * (n + 1) := by
  have hfirst := sampleExecution_query_bound policy history cutter cached total cells (value start)
  have hsecond := sampleExecution_query_bound policy
    (firstRun policy history cutter cached total cells start).2 cutter cached total cells
    (value (start + project amount))
  change (firstRun policy history cutter cached total cells start).2.length ≤ _ at hfirst
  change (secondRun policy history cutter cached total cells amount start).2.length ≤ _ at hsecond
  omega

theorem stage_cut_bound (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) (start : Circle) :
    ((secondRun policy history cutter cached total cells amount start).2.map Prod.fst).countP isCut ≤
      (history.map Prod.fst).countP isCut + 2 := by
  have hfirst := sampleExecution_cut_bound policy history cutter cached total cells (value start)
  have hsecond := sampleExecution_cut_bound policy
    (firstRun policy history cutter cached total cells start).2 cutter cached total cells
    (value (start + project amount))
  change ((firstRun policy history cutter cached total cells start).2.map Prod.fst).countP isCut ≤ _
    at hfirst
  change ((secondRun policy history cutter cached total cells amount start).2.map Prod.fst).countP
    isCut ≤ _ at hsecond
  omega

theorem unconditional_query_bound (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) :
    (∫⁻ start, ((secondRun policy history cutter cached total cells amount start).2.length -
      history.length : ℕ) ∂(volume : Measure Circle)) ≤ 2 * (n + 1) := by
  calc
    _ ≤ ∫⁻ _start : Circle, (2 * (n + 1) : ℝ≥0∞) := by
      apply lintegral_mono
      intro start
      have h := stage_query_bound policy history cutter cached total cells amount start
      dsimp only
      exact_mod_cast (show (secondRun policy history cutter cached total cells amount start).2.length -
        history.length ≤ 2 * (n + 1) by omega)
    _ = _ := by simp

theorem unconditional_cut_bound (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cells : List Component) (amount : I) :
    (∫⁻ start, (((secondRun policy history cutter cached total cells amount start).2.map Prod.fst).countP
      isCut - (history.map Prod.fst).countP isCut : ℕ) ∂(volume : Measure Circle)) ≤ 2 := by
  calc
    _ ≤ ∫⁻ _start : Circle, (2 : ℝ≥0∞) := by
      apply lintegral_mono
      intro start
      have h := stage_cut_bound policy history cutter cached total cells amount start
      dsimp only
      exact_mod_cast (show ((secondRun policy history cutter cached total cells amount start).2.map
        Prod.fst).countP isCut - (history.map Prod.fst).countP isCut ≤ 2 by omega)
    _ = _ := by simp

section PhysicalLaws

variable (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (history : History n) (cutter : Fin n) (cached : Component → ℝ)
  (cells : List Component) (hordered : Ordered cells) (hdisjoint : DisjointComponents cells)
  (hcache : ∀ c ∈ cells, cached c = mass (μ cutter) c)
  (hpositive : 0 < (μ cutter).real (domain cells))

include hpolicy hordered hdisjoint hcache hpositive

theorem first_cdf (start : Circle) :
    cdf (cond (μ cutter) (domain cells))
      (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).1 =
      (value start : ℝ) :=
  (sampleExecution_spec μ policy hpolicy history cutter cached cells hordered hdisjoint hcache
    hpositive (value start) (value_positive start)).2.1

theorem second_cdf (amount : I) (start : Circle) :
    cdf (cond (μ cutter) (domain cells))
      (secondRun policy history cutter cached ((μ cutter).real (domain cells)) cells amount start).1 =
      (value (start + project amount) : ℝ) :=
  (sampleExecution_spec μ policy hpolicy
    (firstRun policy history cutter cached ((μ cutter).real (domain cells)) cells start).2
    cutter cached cells hordered hdisjoint hcache hpositive
    (value (start + project amount)) (value_positive _)).2.1

/-- Every start gives the exact requested fraction of the physical cutter
mass, including boundary-reuse and plateau cases. -/
theorem exact_cutter_mass (amount : I) (start : Circle) :
    (μ cutter).real (piece policy history cutter cached ((μ cutter).real (domain cells))
      cells amount start) = (amount : ℝ) * (μ cutter).real (domain cells) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  have hown := physicalPiece_own_value (cond (μ cutter) (domain cells)) (domain cells)
    (ae_cond_mem (domain_measurable cells)) amount start _ _
    (first_cdf μ policy hpolicy history cutter cached cells hordered hdisjoint hcache hpositive start)
    (second_cdf μ policy hpolicy history cutter cached cells hordered hdisjoint hcache hpositive amount start)
  have hsub : piece policy history cutter cached ((μ cutter).real (domain cells))
      cells amount start ⊆ domain cells := physicalPiece_subset _ _ _ _ _
  change (cond (μ cutter) (domain cells)).real
    (piece policy history cutter cached ((μ cutter).real (domain cells)) cells amount start) = _ at hown
  rw [measureReal_def, cond_apply (domain_measurable cells),
    inter_eq_right.mpr hsub, ENNReal.toReal_mul, ENNReal.toReal_inv] at hown
  change ((μ cutter).real (domain cells))⁻¹ * (μ cutter).real
    (piece policy history cutter cached ((μ cutter).real (domain cells)) cells amount start) = _ at hown
  apply (div_eq_iff hpositive.ne').mp
  simpa only [div_eq_mul_inv, mul_comm] using hown

/-- The physical union construction has the exact arbitrary-foreign-mass
expectation under every jointly measurable admissible history policy. -/
theorem foreign_mass_expectation (hmeas : MeasurablePolicy policy) (amount : I)
    (foreign : Measure ℝ) [SFinite foreign] :
    (∫⁻ start, foreign (piece policy history cutter cached ((μ cutter).real (domain cells))
      cells amount start) ∂(volume : Measure Circle)) =
      ENNReal.ofReal (amount : ℝ) * foreign (domain cells) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  apply physical_foreign_mass_expectation (domain cells) (domain_measurable cells) foreign amount
    _ _
    (measurable_fst.comp (firstRun_measurable policy hmeas history cutter cached _ cells))
    (measurable_fst.comp (secondRun_measurable policy hmeas history cutter cached _ cells amount))
    (monotone_cdf (cond (μ cutter) (domain cells)))
  · intro x _
    exact ⟨cdf_nonneg _ x, cdf_le_one _ x⟩
  · exact ae_of_all _ (first_cdf μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive)
  · exact ae_of_all _ (second_cdf μ policy hpolicy history cutter cached cells
      hordered hdisjoint hcache hpositive amount)

end PhysicalLaws

end EnvyFreeResearch.Full.UpperUnionCircular
