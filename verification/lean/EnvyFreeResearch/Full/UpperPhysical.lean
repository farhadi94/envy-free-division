import EnvyFreeResearch.Full.UpperCircular

/-!
# Real endpoint realization of circular pieces

This module connects circular value coordinates to literal interval unions and
complements built from two arbitrary legal roots. It does not implement the
recorded-domain query ledger or Repair.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval
open scoped Classical

namespace EnvyFreeResearch.Full.UpperPhysical

open UpperCircular UpperProbability

abbrev Circle := UpperCircular.Circle

theorem project_value (z : Circle) : project (value z) = z := by
  exact AddCircle.coe_equivIoc

theorem value_real {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (value (x : Circle) : ℝ) = x := by
  change ((AddCircle.equivIoc 1 0) (x : Circle)).val = x
  rw [AddCircle.equivIoc_coe_eq (show x ∈ Ioc (0 : ℝ) (0 + 1) from
    ⟨hx0, by simpa using hx1⟩)]

theorem value_real_nonpos {x : ℝ} (hx0 : -1 < x) (hx1 : x ≤ 0) :
    (value (x : Circle) : ℝ) = x + 1 := by
  rw [← AddCircle.coe_add_period (1 : ℝ) x]
  exact value_real (by linarith) (by linarith)

theorem value_real_above_one {x : ℝ} (hx0 : 1 < x) (hx1 : x ≤ 2) :
    (value (x : Circle) : ℝ) = x - 1 := by
  have heq : (x : Circle) = ((x - 1 : ℝ) : Circle) := by
    have h := AddCircle.coe_add_period (1 : ℝ) (x - 1)
    simpa only [sub_add_cancel] using h
  rw [heq]
  exact value_real (by linarith) (by linarith)

theorem value_positive (start : Circle) : 0 < (value start : ℝ) :=
  (AddCircle.equivIoc 1 0 start).property.1

theorem endpoint_target_no_wrap (start : Circle) (amount : I)
    (hsum : (value start : ℝ) + amount ≤ 1) :
    (value (start + project amount) : ℝ) = (value start : ℝ) + amount := by
  conv_lhs => rw [← project_value start]
  change (value (((value start : ℝ) + amount : ℝ) : Circle) : ℝ) = _
  exact value_real (by linarith [value_positive start, amount.property.1]) hsum

theorem endpoint_target_wrap (start : Circle) (amount : I)
    (hsum : 1 < (value start : ℝ) + amount) :
    (value (start + project amount) : ℝ) = (value start : ℝ) + amount - 1 := by
  conv_lhs => rw [← project_value start]
  change (value (((value start : ℝ) + amount : ℝ) : Circle) : ℝ) = _
  exact value_real_above_one hsum (by linarith [(value start).property.2, amount.property.2])

/-- The coordinate arc has the usual one-interval/two-interval description.
The exceptional start ending exactly at the circular join is excluded here;
it is one null uniform target, handled explicitly in the probabilistic step. -/
theorem coordinate_arc_iff (start : Circle) (amount : I) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu1 : (value start : ℝ) < 1)
    (ht0 : 0 < (amount : ℝ)) (ht1 : (amount : ℝ) < 1)
    (hsum : (value start : ℝ) + amount ≠ 1) :
    value ((c : Circle) - start) ≤ amount ↔
      if value start < value (start + project amount) then
        (value start : ℝ) < c ∧ c ≤ value (start + project amount)
      else c ≤ value (start + project amount) ∨ (value start : ℝ) < c := by
  let u : ℝ := value start
  have hu0 : 0 < u := value_positive start
  have hrepr :
      (value ((c : Circle) - start) : ℝ) =
        if u < c then c - u else c - u + 1 := by
    rw [← project_value start]
    change (value ((c - u : ℝ) : Circle) : ℝ) = _
    split_ifs with huc
    · exact value_real (by linarith) (by linarith)
    · exact value_real_nonpos (by dsimp [u] at *; linarith)
        (by linarith)
  change (value ((c : Circle) - start) : ℝ) ≤ amount ↔ _
  rw [hrepr]
  rcases lt_or_gt_of_ne hsum with hn | hw
  · have hv := endpoint_target_no_wrap start amount hn.le
    have horder : value start < value (start + project amount) := by
      change (value start : ℝ) < value (start + project amount)
      rw [hv]
      linarith
    rw [ite_eq_left horder, hv]
    dsimp [u] at *
    split_ifs with huc
    · constructor
      · intro h
        exact ⟨huc, by linarith⟩
      · rintro ⟨_, h⟩
        linarith
    · constructor
      · intro h
        exfalso
        linarith
      · rintro ⟨h, _⟩
        exact False.elim (huc h)
  · have hv := endpoint_target_wrap start amount hw
    have horder : ¬ value start < value (start + project amount) := by
      change ¬ (value start : ℝ) < value (start + project amount)
      rw [hv]
      linarith
    rw [ite_eq_right horder, hv]
    dsimp [u] at *
    split_ifs with huc
    · constructor
      · intro _
        exact Or.inr huc
      · intro _
        linarith
    · constructor
      · intro h
        exact Or.inl (by linarith)
      · intro h
        rcases h with h | h <;> linarith

/-- A literal physical piece with at most two new boundaries. Zero amounts
are empty and full amounts retain every fragment of the recorded domain. -/
def physicalPiece (domain : Set ℝ) (amount : I) (start : Circle)
    (first last : ℝ) : Set ℝ :=
  if amount = 0 then ∅ else if amount = 1 then domain else
    if value start < value (start + project amount) then domain ∩ Ioc first last
    else domain \ Ioc last first

theorem physicalPiece_zero (domain : Set ℝ) (start : Circle) (first last : ℝ) :
    physicalPiece domain 0 start first last = ∅ := by simp [physicalPiece]

theorem physicalPiece_one (domain : Set ℝ) (start : Circle) (first last : ℝ) :
    physicalPiece domain 1 start first last = domain := by simp [physicalPiece]

theorem physicalPiece_subset (domain : Set ℝ) (amount : I) (start : Circle)
    (first last : ℝ) : physicalPiece domain amount start first last ⊆ domain := by
  unfold physicalPiece
  split_ifs <;> intro x hx
  · exact False.elim hx
  · exact hx
  · exact hx.1
  · exact hx.1

theorem legal_root_lt_iff {F : ℝ → ℝ} (hF : Monotone F)
    {target root x : ℝ} (hroot : F root = target) (hne : target ≠ F x) :
    root < x ↔ target < F x := by
  constructor
  · intro h
    have hle : target ≤ F x := by simpa only [hroot] using hF h.le
    exact lt_of_le_of_ne hle hne
  · intro h
    by_contra hbad
    have hh := hF (le_of_not_gt hbad)
    rw [hroot] at hh
    exact (not_le_of_gt h) hh

/-- Exact membership comparison between the physical two-cut piece and its
value-coordinate arc, outside the two target levels of the fixed point. -/
theorem physical_membership_iff (domain : Set ℝ) (amount : I) (start : Circle)
    {F : ℝ → ℝ} (hF : Monotone F) {first last x : ℝ}
    (hfirst : F first = (value start : ℝ))
    (hlast : F last = (value (start + project amount) : ℝ))
    (hx0 : 0 ≤ F x) (hx1 : F x ≤ 1)
    (hu1 : (value start : ℝ) < 1)
    (ht0 : 0 < (amount : ℝ)) (ht1 : (amount : ℝ) < 1)
    (hsum : (value start : ℝ) + amount ≠ 1)
    (hneFirst : (value start : ℝ) ≠ F x)
    (hneLast : (value (start + project amount) : ℝ) ≠ F x) :
    x ∈ physicalPiece domain amount start first last ↔
      x ∈ domain ∧ value ((F x : Circle) - start) ≤ amount := by
  have htne0 : amount ≠ 0 := by intro h; simp [h] at ht0
  have htne1 : amount ≠ 1 := by intro h; simp [h] at ht1
  have hfx := legal_root_lt_iff hF hfirst hneFirst
  have hlx := legal_root_lt_iff hF hlast hneLast
  have hxf : x ≤ first ↔ F x ≤ (value start : ℝ) := by
    simpa only [not_lt] using not_congr hfx
  have hxl : x ≤ last ↔ F x ≤ (value (start + project amount) : ℝ) := by
    simpa only [not_lt] using not_congr hlx
  rw [coordinate_arc_iff start amount hx0 hx1 hu1 ht0 ht1 hsum]
  unfold physicalPiece
  rw [ite_eq_right htne0, ite_eq_right htne1]
  split_ifs
  · simp only [mem_inter_iff, mem_Ioc, hfx, hxl]
  · simp only [Set.mem_sdiff, mem_Ioc, hlx, hxf, not_and_or, not_lt, not_le]

/-- The literal two-cut piece has the prescribed cutter value for every
admissible pair of responses, including the circular-join targets. -/
theorem physicalPiece_own_value (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (domain : Set ℝ) (hsupport : ∀ᵐ x ∂μ, x ∈ domain)
    (amount : I) (start : Circle) (first last : ℝ)
    (hfirst : cdf μ first = (value start : ℝ))
    (hlast : cdf μ last = (value (start + project amount) : ℝ)) :
    μ.real (physicalPiece domain amount start first last) = (amount : ℝ) := by
  have hdomain : μ.real domain = 1 := by
    calc
      μ.real domain = μ.real univ := by
        apply measureReal_congr
        filter_upwards [hsupport] with x hx
        simp [hx]
      _ = 1 := probReal_univ
  have hinter (s : Set ℝ) : μ.real (domain ∩ s) = μ.real s := by
    apply measureReal_congr
    filter_upwards [hsupport] with x hx
    simp [hx]
  have hdiff (s : Set ℝ) : μ.real (domain \ s) = μ.real sᶜ := by
    apply measureReal_congr
    filter_upwards [hsupport] with x hx
    simp [hx]
  by_cases ht0 : amount = 0
  · simp [ht0, physicalPiece]
  by_cases ht1 : amount = 1
  · simp [ht1, physicalPiece, hdomain]
  have htpos : 0 < (amount : ℝ) := by
    have htne : (amount : ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
    exact lt_of_le_of_ne amount.property.1 htne.symm
  have htlt : (amount : ℝ) < 1 := by
    have htne : (amount : ℝ) ≠ 1 := fun h => ht1 (Subtype.ext h)
    exact lt_of_le_of_ne amount.property.2 htne
  unfold physicalPiece
  rw [ite_eq_right ht0, ite_eq_right ht1]
  by_cases hsum : (value start : ℝ) + amount ≤ 1
  · have hv := endpoint_target_no_wrap start amount hsum
    have horder : value start < value (start + project amount) := by
      change (value start : ℝ) < value (start + project amount)
      rw [hv]
      linarith
    rw [ite_eq_left horder, hinter]
    have hioc : μ (Ioc first last) = ENNReal.ofReal (amount : ℝ) := by
      rw [← measure_cdf μ, StieltjesFunction.measure_Ioc, hfirst, hlast, hv]
      congr 1
      ring
    rw [measureReal_def, hioc, ENNReal.toReal_ofReal amount.property.1]
  · have hv := endpoint_target_wrap start amount (lt_of_not_ge hsum)
    have horder : ¬ value start < value (start + project amount) := by
      change ¬ (value start : ℝ) < value (start + project amount)
      rw [hv]
      linarith
    rw [ite_eq_right horder, hdiff, measureReal_compl measurableSet_Ioc, probReal_univ]
    have hioc : μ (Ioc last first) = ENNReal.ofReal (1 - (amount : ℝ)) := by
      rw [← measure_cdf μ, StieltjesFunction.measure_Ioc, hfirst, hlast, hv]
      congr 1
      ring
    rw [measureReal_def, hioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - (amount : ℝ))]
    ring

/-- A fixed real value level is avoided by the fresh circular target. -/
theorem value_ne_ae (c : ℝ) :
    ∀ᵐ start ∂(volume : Measure Circle), (value start : ℝ) ≠ c := by
  have hp := unitInterval.measurePreserving_coe.comp value_preserves_volume
  apply (hp.hasLaw.ae_iff
    (measurableSet_setOfPred.mp (measurableSet_singleton c).compl)).mpr
  exact Measure.ae_ne _ c

theorem shifted_value_ne_ae (shift : Circle) (c : ℝ) :
    ∀ᵐ start ∂(volume : Measure Circle), (value (start + shift) : ℝ) ≠ c := by
  have hp := unitInterval.measurePreserving_coe.comp (shifted_value_preserves_volume shift)
  apply (hp.hasLaw.ae_iff
    (measurableSet_setOfPred.mp (measurableSet_singleton c).compl)).mpr
  exact Measure.ae_ne _ c

/-- Every fixed physical point has the claimed inclusion probability under
arbitrary measurable, history-dependent legal endpoint choices. The endpoint
choices may share their random start and are not assumed independent. -/
theorem physical_point_inclusion (domain : Set ℝ) (amount : I)
    (first last : Circle → ℝ) {F : ℝ → ℝ} (hF : Monotone F)
    (hrange : ∀ x ∈ domain, 0 ≤ F x ∧ F x ≤ 1)
    (hfirst : ∀ᵐ start ∂(volume : Measure Circle),
      F (first start) = (value start : ℝ))
    (hlast : ∀ᵐ start ∂(volume : Measure Circle),
      F (last start) = (value (start + project amount) : ℝ))
    (x : ℝ) :
    (volume : Measure Circle)
        {start | x ∈ physicalPiece domain amount start (first start) (last start)} =
      if x ∈ domain then ENNReal.ofReal (amount : ℝ) else 0 := by
  classical
  by_cases hx : x ∈ domain
  · rw [ite_eq_left hx]
    by_cases ht0 : amount = 0
    · simp [ht0, physicalPiece]
    by_cases ht1 : amount = 1
    · simp [ht1, physicalPiece, hx]
    have htpos : 0 < (amount : ℝ) := by
      have htne : (amount : ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
      exact lt_of_le_of_ne amount.property.1 htne.symm
    have htlt : (amount : ℝ) < 1 := by
      have htne : (amount : ℝ) ≠ 1 := fun h => ht1 (Subtype.ext h)
      exact lt_of_le_of_ne amount.property.2 htne
    have heq :
        {start | x ∈ physicalPiece domain amount start (first start) (last start)}
          =ᵐ[(volume : Measure Circle)]
        {start | value ((F x : Circle) - start) ≤ amount} := by
      filter_upwards [hfirst, hlast, value_ne_ae 1,
        value_ne_ae (1 - (amount : ℝ)), value_ne_ae (F x),
        shifted_value_ne_ae (project amount) (F x)] with start hf hl hu hsum hnf hnl
      apply propext
      have hmembership := physical_membership_iff domain amount start hF hf hl
        (hrange x hx).1 (hrange x hx).2
        (lt_of_le_of_ne (value start).property.2 hu) htpos htlt
        (by intro h; apply hsum; linarith) hnf hnl
      simpa only [hx, true_and] using hmembership
    rw [measure_congr heq]
    exact point_inclusion (F x : Circle) amount
  · rw [ite_eq_right hx]
    have hempty :
        {start | x ∈ physicalPiece domain amount start (first start) (last start)} = ∅ := by
      ext start
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact hx (physicalPiece_subset domain amount start _ _ h)
    rw [hempty, measure_empty]

theorem measurable_physical_membership (domain : Set ℝ) (hdomain : MeasurableSet domain)
    (amount : I) (first last : Circle → ℝ) (hfirst : Measurable first)
    (hlast : Measurable last) :
    MeasurableSet {p : Circle × ℝ |
      p.2 ∈ physicalPiece domain amount p.1 (first p.1) (last p.1)} := by
  classical
  unfold physicalPiece
  by_cases ht0 : amount = 0
  · simp only [ht0, ite_true, mem_empty_iff_false, ofPred_false, MeasurableSet.empty]
  simp only [ht0, ite_false]
  by_cases ht1 : amount = 1
  · simp only [ht1, ite_true]
    exact hdomain.preimage measurable_snd
  simp only [ht1, ite_false]
  have horder : MeasurableSet {p : Circle × ℝ |
      value p.1 < value (p.1 + project amount)} :=
    measurableSet_lt (measurable_value.comp measurable_fst)
      (measurable_value.comp (measurable_fst.add_const _))
  have hforward : MeasurableSet {p : Circle × ℝ |
      p.2 ∈ domain ∩ Ioc (first p.1) (last p.1)} :=
    (hdomain.preimage measurable_snd).inter
      ((measurableSet_lt (hfirst.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hlast.comp measurable_fst)))
  have hbackward : MeasurableSet {p : Circle × ℝ |
      p.2 ∈ domain \ Ioc (last p.1) (first p.1)} :=
    (hdomain.preimage measurable_snd).diff
      ((measurableSet_lt (hlast.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hfirst.comp measurable_fst)))
  convert (horder.inter hforward).union (horder.compl.inter hbackward) using 1
  ext p
  by_cases h : value p.1 < value (p.1 + project amount) <;> simp [h]

/-- The actual two-cut physical construction satisfies the foreign-mass
expectation identity. This is an unconditional integral over the fresh start,
including all plateau choices allowed by the given endpoint response functions. -/
theorem physical_foreign_mass_expectation
    (domain : Set ℝ) (hdomain : MeasurableSet domain)
    (foreign : Measure ℝ) [SFinite foreign] (amount : I)
    (first last : Circle → ℝ) (hfirstMeas : Measurable first) (hlastMeas : Measurable last)
    {F : ℝ → ℝ} (hF : Monotone F)
    (hrange : ∀ x ∈ domain, 0 ≤ F x ∧ F x ≤ 1)
    (hfirst : ∀ᵐ start ∂(volume : Measure Circle),
      F (first start) = (value start : ℝ))
    (hlast : ∀ᵐ start ∂(volume : Measure Circle),
      F (last start) = (value (start + project amount) : ℝ)) :
    (∫⁻ start, foreign (physicalPiece domain amount start (first start) (last start))
      ∂(volume : Measure Circle)) = ENNReal.ofReal (amount : ℝ) * foreign domain := by
  classical
  let S : Set (Circle × ℝ) :=
    {p | p.2 ∈ physicalPiece domain amount p.1 (first p.1) (last p.1)}
  have hS : MeasurableSet S :=
    measurable_physical_membership domain hdomain amount first last hfirstMeas hlastMeas
  calc
    _ = ((volume : Measure Circle).prod foreign) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ x, (volume : Measure Circle)
        {start | x ∈ physicalPiece domain amount start (first start) (last start)} ∂foreign :=
      Measure.prod_apply_symm hS
    _ = ∫⁻ x, domain.indicator (fun _ => ENNReal.ofReal (amount : ℝ)) x ∂foreign := by
      apply lintegral_congr
      intro x
      simpa only [indicator_apply] using
        physical_point_inclusion domain amount first last hF hrange hfirst hlast x
    _ = _ := lintegral_indicator_const hdomain _

end EnvyFreeResearch.Full.UpperPhysical
