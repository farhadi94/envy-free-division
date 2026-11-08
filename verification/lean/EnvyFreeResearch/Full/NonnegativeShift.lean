import EnvyFreeResearch.Full.NonnegativeGeometry

/-!
# The manuscript's independent uniform shift law

This file uses the literal real offset law on `(-w,w]`, independently of a
uniform circular first center. The endpoint convention has no effect. This
provides a single actual law for the sharp interval-separation and arbitrary-
fragmentation same-owner bounds.
-/

namespace EnvyFreeResearch.Full.NonnegativeShift

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Circle := NonnegativeCircle.Circle
open NonnegativeGeometry (arc measurable_arc fixed_shift_separation_le)

noncomputable def offsetLaw (w : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * w))⁻¹ • volume.restrict (Ioc (-w) w)

noncomputable def shiftLaw (w : ℝ) : Measure (ℝ × Circle) :=
  (offsetLaw w).prod volume

def first (z : ℝ × Circle) : Circle := z.2

def second (z : ℝ × Circle) : Circle := z.2 + (z.1 : Circle)

theorem measurable_first : Measurable first := measurable_snd

theorem measurable_second : Measurable second :=
  measurable_snd.add (AddCircle.measurable_mk'.comp measurable_fst)

theorem offsetLaw_probability (w : ℝ) (hw : 0 < w) : IsProbabilityMeasure (offsetLaw w) := by
  constructor
  rw [offsetLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter, Real.volume_Ioc, sub_neg_eq_add, smul_eq_mul]
  have hsame : w + w = 2 * w := by ring
  rw [hsame, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top]

theorem shiftLaw_probability (w : ℝ) (hw : 0 < w) : IsProbabilityMeasure (shiftLaw w) := by
  let := offsetLaw_probability w hw
  exact inferInstanceAs (IsProbabilityMeasure ((offsetLaw w).prod volume))

theorem first_marginal (w : ℝ) (hw : 0 < w) {A : Set Circle} (hA : MeasurableSet A) :
    shiftLaw w (first ⁻¹' A) = volume A := by
  let := offsetLaw_probability w hw
  rw [shiftLaw, Measure.prod_apply (hA.preimage measurable_first)]
  have hsection (u : ℝ) : volume (Prod.mk u ⁻¹' (first ⁻¹' A)) = volume A := rfl
  simp_rw [hsection]
  simp

theorem second_marginal (w : ℝ) (hw : 0 < w) {A : Set Circle} (hA : MeasurableSet A) :
    shiftLaw w (second ⁻¹' A) = volume A := by
  let := offsetLaw_probability w hw
  rw [shiftLaw, Measure.prod_apply (hA.preimage measurable_second)]
  have hsection (u : ℝ) : volume (Prod.mk u ⁻¹' (second ⁻¹' A)) = volume A :=
    measure_preimage_add_right volume (u : Circle) A
  simp_rw [hsection]
  simp

theorem circle_singleton_mass (a : Circle) : volume ({a} : Set Circle) = 0 := by
  have h := AddCircle.volume_closedBall (1 : ℝ) (x := a) (0 : ℝ)
  simpa using h

theorem first_atomless (w : ℝ) (hw : 0 < w) (a : Circle) :
    shiftLaw w {z | first z = a} = 0 := by
  change shiftLaw w (first ⁻¹' {a}) = 0
  rw [first_marginal w hw (measurableSet_singleton a), circle_singleton_mass]

theorem second_atomless (w : ℝ) (hw : 0 < w) (a : Circle) :
    shiftLaw w {z | second z = a} = 0 := by
  change shiftLaw w (second ⁻¹' {a}) = 0
  rw [second_marginal w hw (measurableSet_singleton a), circle_singleton_mass]

/-- The unnormalized first absolute moment of the real uniform-offset window. -/
theorem integral_abs_offset (w : ℝ) (hw : 0 ≤ w) :
    (∫ u in Ioc (-w) w, |u|) = w ^ 2 := by
  have hleft : (∫ u in Ioc (-w) 0, |u|) = w ^ 2 / 2 := by
    have h := integral_pow_abs_sub_uIoc (a := 0) (b := -w) 1
    norm_num [uIoc_of_ge (show -w ≤ 0 by linarith), abs_of_nonneg hw] at h
    exact h
  have hright : (∫ u in Ioc 0 w, |u|) = w ^ 2 / 2 := by
    have h := integral_pow_abs_sub_uIoc (a := 0) (b := w) 1
    norm_num [uIoc_of_le hw, abs_of_nonneg hw] at h
    exact h
  have hsplit : Ioc (-w) w = Ioc (-w) 0 ∪ Ioc 0 w := by
    ext u
    simp only [mem_Ioc, mem_union]
    constructor
    · intro hu
      by_cases h : u ≤ 0
      · exact Or.inl ⟨hu.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, hu.2⟩
    · rintro (hu | hu) <;> constructor <;> linarith [hu.1, hu.2]
  have hdisjoint : Disjoint (Ioc (-w) 0) (Ioc 0 w) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    linarith [hu.2, hv.1]
  have hint (a b : ℝ) : IntegrableOn (fun u : ℝ => |u|) (Ioc a b) volume :=
    continuous_abs.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [hsplit, setIntegral_union hdisjoint measurableSet_Ioc (hint _ _) (hint _ _), hleft, hright]
  ring

theorem mean_twice_abs_offset (w : ℝ) (hw : 0 < w) :
    (∫⁻ u, ENNReal.ofReal (2 * |u|) ∂offsetLaw w) = ENNReal.ofReal w := by
  have hint : Integrable (fun u : ℝ => 2 * |u|) (volume.restrict (Ioc (-w) w)) :=
    (continuous_const.mul continuous_abs).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hintegral : (∫ u in Ioc (-w) w, 2 * |u|) = 2 * w ^ 2 := by
    rw [integral_const_mul, integral_abs_offset w hw.le]
  rw [offsetLaw, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (by intro u; positivity))]
  rw [hintegral, smul_eq_mul]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem measurable_separation (a b : ℝ) :
    MeasurableSet {z : ℝ × Circle | (first z ∈ arc a b) ≠ (second z ∈ arc a b)} := by
  have hA := (measurable_arc a b).preimage measurable_first
  have hB := (measurable_arc a b).preimage measurable_second
  have heq : {z : ℝ × Circle | (first z ∈ arc a b) ≠ (second z ∈ arc a b)} =
      (first ⁻¹' arc a b) \ (second ⁻¹' arc a b) ∪
      (second ⁻¹' arc a b) \ (first ⁻¹' arc a b) := by
    ext z
    simp only [mem_ofPred_eq, mem_union, mem_sdiff, mem_preimage]
    tauto
  rw [heq]
  exact (hA.diff hB).union (hB.diff hA)

/-- Exact manuscript constant `w`: this is a probability bound for the actual
continuous independent offset/center law, not an assumed detection rate. -/
theorem separation_probability_le (a b w : ℝ) (hw : 0 < w) :
    shiftLaw w {z | (first z ∈ arc a b) ≠ (second z ∈ arc a b)} ≤ ENNReal.ofReal w := by
  rw [shiftLaw, Measure.prod_apply (measurable_separation a b)]
  calc
    (∫⁻ u, volume (Prod.mk u ⁻¹'
        {z | (first z ∈ arc a b) ≠ (second z ∈ arc a b)}) ∂offsetLaw w) ≤
        ∫⁻ u, ENNReal.ofReal (2 * |u|) ∂offsetLaw w := by
      apply lintegral_mono
      intro u
      exact fixed_shift_separation_le a b u
    _ = ENNReal.ofReal w := mean_twice_abs_offset w hw

/-- Restricting the offset to a window shorter than one full fundamental
interval bounds each second-center fiber by its whole circular Haar mass. -/
theorem offset_fiber_le (w : ℝ) (hwsmall : w ≤ 1 / 2)
    (x : Circle) {A : Set Circle} (hA : MeasurableSet A) :
    offsetLaw w {u | x + (u : Circle) ∈ A} ≤
      (ENNReal.ofReal (2 * w))⁻¹ * volume A := by
  have hsubset : Ioc (-w) w ⊆ Ioc (-w) (-w + 1) := by
    intro u hu
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hmp := (measurePreserving_add_left (volume : Measure Circle) x).comp
    (AddCircle.measurePreserving_mk (1 : ℝ) (-w))
  have hfundamental : (volume.restrict (Ioc (-w) (-w + 1)))
      {u : ℝ | x + (u : Circle) ∈ A} = volume A := by
    exact hmp.measure_preimage hA.nullMeasurableSet
  rw [offsetLaw, Measure.smul_apply, smul_eq_mul]
  gcongr
  exact ((Measure.restrict_mono_set volume hsubset) _).trans_eq hfundamental

/-- The same-owner probability for the very same law used in the sharp
separation theorem. Equal bundle mass is the only partition property needed;
there is no component-count hypothesis. -/
theorem same_owner_le {Agent : Type*} [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [Countable Agent]
    (owner : Circle → Agent) (howner : Measurable owner) (b : ℝ≥0∞)
    (hfibers : ∀ agent, volume (owner ⁻¹' {agent}) = b)
    (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2) :
    shiftLaw w {z | owner (first z) = owner (second z)} ≤
      (ENNReal.ofReal (2 * w))⁻¹ * b := by
  let := offsetLaw_probability w hw
  have hmeas : MeasurableSet {z : ℝ × Circle | owner (first z) = owner (second z)} :=
    measurableSet_eq_fun (howner.comp measurable_first) (howner.comp measurable_second)
  rw [shiftLaw, Measure.prod_apply_symm hmeas]
  calc
    (∫⁻ x : Circle, offsetLaw w ((fun u : ℝ => (u, x)) ⁻¹'
        {z | owner (first z) = owner (second z)})) ≤
        ∫⁻ _x : Circle, (ENNReal.ofReal (2 * w))⁻¹ * b := by
      apply lintegral_mono
      intro x
      have hbound := offset_fiber_le w hwsmall x
        (howner (measurableSet_singleton (owner x)))
      rw [hfibers (owner x)] at hbound
      change offsetLaw w {u | owner x = owner (x + (u : Circle))} ≤ _
      have hset : {u : ℝ | x + (u : Circle) ∈ owner ⁻¹' {owner x}} =
          {u : ℝ | owner x = owner (x + (u : Circle))} := by
        ext u
        simp [eq_comm]
      rw [hset] at hbound
      exact hbound
    _ = (ENNReal.ofReal (2 * w))⁻¹ * b := by simp

end EnvyFreeResearch.Full.NonnegativeShift

#print axioms EnvyFreeResearch.Full.NonnegativeShift.first_marginal
#print axioms EnvyFreeResearch.Full.NonnegativeShift.second_marginal
#print axioms EnvyFreeResearch.Full.NonnegativeShift.mean_twice_abs_offset
#print axioms EnvyFreeResearch.Full.NonnegativeShift.separation_probability_le
#print axioms EnvyFreeResearch.Full.NonnegativeShift.same_owner_le
