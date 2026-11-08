import EnvyFreeResearch.Full.UpperRecordedDomain

/-!
# Independent physical reserve labels

The reserve is generated from a finite product of ordinary uniform real draws.
Its mean, variance, and failure probabilities are derived from that product law;
none is assumed as a probabilistic primitive.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval BigOperators

namespace EnvyFreeResearch.Full.UpperReserve

/-- Retain a coarse parent exactly when its own uniform draw is at most `q`. -/
def mark (q draw : I) : ℝ := (Iic q).indicator (fun _ => 1) draw

theorem mark_measurable (q : I) : Measurable (mark q) := by
  exact measurable_const.indicator measurableSet_Iic

theorem mark_memLp (q : I) : MemLp (mark q) 2 (volume : Measure I) := by
  exact (memLp_const (1 : ℝ)).indicator measurableSet_Iic.nullMeasurableSet

theorem mark_mean (q : I) : ∫ draw : I, mark q draw = (q : ℝ) := by
  unfold mark
  rw [integral_indicator_const 1 measurableSet_Iic]
  simp [Measure.real, unitInterval.volume_Iic, q.property.1]

theorem mark_square (q draw : I) : (mark q draw) ^ 2 = mark q draw := by
  simp only [mark, indicator_apply]
  split_ifs <;> norm_num

theorem mark_variance (q : I) :
    variance (mark q) volume = (q : ℝ) * (1 - (q : ℝ)) := by
  rw [variance_eq_sub (mark_memLp q), mark_mean]
  have hsq : (mark q) ^ 2 = mark q := by
    funext draw
    exact mark_square q draw
  rw [hsq, mark_mean]
  ring

variable {Cell : Type*} [Fintype Cell]

/-- Every cell receives an independent uniform draw. -/
def labelLaw : Measure (Cell → I) := Measure.pi (fun _ => (volume : Measure I))

instance labelLaw_probability : IsProbabilityMeasure (labelLaw (Cell := Cell)) := by
  unfold labelLaw
  infer_instance

/-- The retained mass, computed using already recorded coarse-cell masses. -/
def reserveValue (weights : Cell → ℝ) (q : I) (draws : Cell → I) : ℝ :=
  ∑ c, weights c * mark q (draws c)

theorem reserveValue_memLp (weights : Cell → ℝ) (q : I) :
    MemLp (reserveValue weights q) 2 labelLaw := by
  apply memLp_finsetSum
  intro c _
  exact ((mark_memLp q).const_mul (weights c)).comp_measurePreserving
    (measurePreserving_eval _ c)

theorem reserveValue_mean (weights : Cell → ℝ) (q : I) :
    ∫ draws, reserveValue weights q draws ∂labelLaw = (q : ℝ) * ∑ c, weights c := by
  unfold reserveValue
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul]
    rw [show (∫ a : Cell → I, mark q (a c) ∂labelLaw) = (q : ℝ) from
      (integral_comp_eval (mark_memLp q).aestronglyMeasurable).trans (mark_mean q)]
    ring
  · intro c _
    exact (((mark_memLp q).const_mul (weights c)).comp_measurePreserving
      (measurePreserving_eval _ c)).integrable (by norm_num)

theorem reserveValue_variance (weights : Cell → ℝ) (q : I) :
    variance (reserveValue weights q) labelLaw =
      ((q : ℝ) * (1 - (q : ℝ))) * ∑ c, (weights c) ^ 2 := by
  have h := variance_sum_pi (fun c => (mark_memLp q).const_mul (weights c))
  have hfun : (∑ c, fun draws : Cell → I => weights c * mark q (draws c)) =
      reserveValue weights q := by
    funext draws
    simp [reserveValue]
  rw [hfun] at h
  change variance (reserveValue weights q) labelLaw = _ at h
  rw [h]
  simp only [variance_const_mul, mark_variance]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem reserveValue_variance_le (weights : Cell → ℝ) (q : I) (eta : ℝ)
    (hnonneg : ∀ c, 0 ≤ weights c) (hsmall : ∀ c, weights c ≤ eta)
    (hnormalized : ∑ c, weights c = 1) :
    variance (reserveValue weights q) labelLaw ≤ (q : ℝ) * eta := by
  have hsum : ∑ c, (weights c) ^ 2 ≤ eta := by
    calc
      ∑ c, (weights c) ^ 2 ≤ ∑ c, eta * weights c := by
        apply Finset.sum_le_sum
        intro c _
        nlinarith [mul_le_mul_of_nonneg_right (hsmall c) (hnonneg c)]
      _ = eta := by rw [← Finset.mul_sum, hnormalized, mul_one]
  have hnon : 0 ≤ ∑ c, (weights c) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [reserveValue_variance]
  calc
    (q : ℝ) * (1 - (q : ℝ)) * ∑ c, (weights c) ^ 2 ≤
        (q : ℝ) * ∑ c, (weights c) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hnon
      nlinarith [q.property.1]
    _ ≤ (q : ℝ) * eta := mul_le_mul_of_nonneg_left hsum q.property.1

/-- A row fails the reserve-mass check precisely outside the required interval. -/
def badMass (weights : Cell → ℝ) (q : I) : Set (Cell → I) :=
  {draws | reserveValue weights q draws < (q : ℝ) / 2 ∨
    3 * (q : ℝ) / 2 < reserveValue weights q draws}

/-- The manuscript's single-row preparation error, from actual independent labels. -/
theorem badMass_probability (weights : Cell → ℝ) (q : I) (eta : ℝ)
    (hq : 0 < (q : ℝ)) (hnonneg : ∀ c, 0 ≤ weights c)
    (hsmall : ∀ c, weights c ≤ eta) (hnormalized : ∑ c, weights c = 1) :
    labelLaw (badMass weights q) ≤ ENNReal.ofReal (4 * eta / (q : ℝ)) := by
  have hmean : (∫ draws, reserveValue weights q draws ∂labelLaw) = (q : ℝ) := by
    rw [reserveValue_mean, hnormalized, mul_one]
  have hsubset : badMass weights q ⊆
      {draws | (q : ℝ) / 2 ≤ |reserveValue weights q draws -
        ∫ draws, reserveValue weights q draws ∂labelLaw|} := by
    intro draws hdraws
    change (q : ℝ) / 2 ≤ |reserveValue weights q draws -
      ∫ draws, reserveValue weights q draws ∂labelLaw|
    rw [hmean]
    rcases hdraws with hlow | hhigh
    · linarith [neg_le_abs (reserveValue weights q draws - (q : ℝ))]
    · linarith [le_abs_self (reserveValue weights q draws - (q : ℝ))]
  calc
    labelLaw (badMass weights q) ≤ labelLaw
        {draws | (q : ℝ) / 2 ≤ |reserveValue weights q draws -
          ∫ draws, reserveValue weights q draws ∂labelLaw|} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (variance (reserveValue weights q) labelLaw / ((q : ℝ) / 2) ^ 2) :=
      meas_ge_le_variance_div_sq (reserveValue_memLp weights q) (by linarith)
    _ ≤ ENNReal.ofReal (4 * eta / (q : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        variance (reserveValue weights q) labelLaw / ((q : ℝ) / 2) ^ 2 ≤
            ((q : ℝ) * eta) / ((q : ℝ) / 2) ^ 2 :=
          div_le_div_of_nonneg_right
            (reserveValue_variance_le weights q eta hnonneg hsmall hnormalized) (sq_nonneg _)
        _ = 4 * eta / (q : ℝ) := by field_simp; ring

/-- All row checks are bounded on the original product probability space. -/
theorem any_badMass_probability {Row : Type*} [Fintype Row]
    (weights : Row → Cell → ℝ) (q : I) (eta : ℝ) (hq : 0 < (q : ℝ))
    (hnonneg : ∀ r c, 0 ≤ weights r c) (hsmall : ∀ r c, weights r c ≤ eta)
    (hnormalized : ∀ r, ∑ c, weights r c = 1) :
    labelLaw (⋃ r, badMass (weights r) q) ≤
      ENNReal.ofReal (4 * (Fintype.card Row : ℝ) * eta / (q : ℝ)) := by
  calc
    labelLaw (⋃ r, badMass (weights r) q) ≤ ∑ r, labelLaw (badMass (weights r) q) := by
      simpa only [tsum_fintype] using
        (measure_iUnion_le (μ := labelLaw) (fun r => badMass (weights r) q))
    _ ≤ ∑ _r : Row, ENNReal.ofReal (4 * eta / (q : ℝ)) :=
      Finset.sum_le_sum (fun r _ => badMass_probability (weights r) q eta hq
        (hnonneg r) (hsmall r) (hnormalized r))
    _ = ENNReal.ofReal (4 * (Fintype.card Row : ℝ) * eta / (q : ℝ)) := by
      rw [show 4 * (Fintype.card Row : ℝ) * eta / (q : ℝ) =
        (Fintype.card Row : ℝ) * (4 * eta / (q : ℝ)) by ring]
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

theorem mark_nonneg (q draw : I) : 0 ≤ mark q draw := by
  simp only [mark, indicator_apply]
  split_ifs <;> norm_num

theorem reserveValue_nonneg (weights : Cell → ℝ) (q : I)
    (hnonneg : ∀ c, 0 ≤ weights c) (draws : Cell → I) :
    0 ≤ reserveValue weights q draws :=
  Finset.sum_nonneg (fun c _ => mul_nonneg (hnonneg c) (mark_nonneg q (draws c)))

/-- Markov's bound for retained refined-cell counts. The weights may be the
integer number of refined children in each coarse parent. -/
theorem reserve_count_probability (counts : Cell → ℝ) (q : I) (cap : ℝ)
    (hcap : 0 < cap) (hnonneg : ∀ c, 0 ≤ counts c) :
    labelLaw {draws | cap < reserveValue counts q draws} ≤
      ENNReal.ofReal ((q : ℝ) * (∑ c, counts c) / cap) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (reserveValue_nonneg counts q hnonneg))
    ((reserveValue_memLp counts q).integrable (by norm_num)) cap
  rw [reserveValue_mean] at hm
  have hbound : labelLaw.real {draws | cap ≤ reserveValue counts q draws} ≤
      (q : ℝ) * (∑ c, counts c) / cap := by
    apply (le_div_iff₀ hcap).mpr
    simpa only [mul_comm] using hm
  calc
    labelLaw {draws | cap < reserveValue counts q draws} ≤
        labelLaw {draws | cap ≤ reserveValue counts q draws} :=
      measure_mono (fun draws h =>
        (show cap < reserveValue counts q draws from h).le)
    _ = ENNReal.ofReal (labelLaw.real {draws | cap ≤ reserveValue counts q draws}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- A preselected parent is retained with exactly probability `q`. -/
theorem parent_marked_probability (q : I) (c : Cell) :
    labelLaw {draws | draws c ≤ q} = ENNReal.ofReal (q : ℝ) := by
  have h := (measurePreserving_eval (fun _ : Cell => (volume : Measure I)) c).measure_preimage
    (s := Iic q) measurableSet_Iic.nullMeasurableSet
  simpa only [labelLaw, preimage, mem_Iic, unitInterval.volume_Iic] using h

/-- The selected parent set is fixed before the fresh independent labels. -/
theorem selected_parent_probability (selected : Finset Cell) (q : I) :
    labelLaw (⋃ c ∈ selected, {draws | draws c ≤ q}) ≤
      ENNReal.ofReal ((selected.card : ℝ) * (q : ℝ)) := by
  calc
    labelLaw (⋃ c ∈ selected, {draws | draws c ≤ q}) ≤
        ∑ c ∈ selected, labelLaw {draws | draws c ≤ q} := measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((selected.card : ℝ) * (q : ℝ)) := by
      simp [parent_marked_probability, ENNReal.ofReal_mul, nsmul_eq_mul]

open UpperRecordedDomain

def retainedCarrier (cells : Cell → Component) (q : I) (draws : Cell → I)
    (c : Cell) : Set ℝ := if draws c ≤ q then (cells c).carrier else ∅

/-- The literal reserve is the union of independently retained physical parents. -/
def physicalReserve (cells : Cell → Component) (q : I) (draws : Cell → I) : Set ℝ :=
  ⋃ c, retainedCarrier cells q draws c

omit [Fintype Cell] in
theorem retainedCarrier_measurable (cells : Cell → Component) (q : I) (draws : Cell → I)
    (c : Cell) : MeasurableSet (retainedCarrier cells q draws c) := by
  unfold retainedCarrier
  split_ifs
  · exact (cells c).measurable_carrier
  · exact MeasurableSet.empty

omit [Fintype Cell] in
theorem retainedCarrier_subset (cells : Cell → Component) (q : I) (draws : Cell → I)
    (c : Cell) : retainedCarrier cells q draws c ⊆ (cells c).carrier := by
  unfold retainedCarrier
  split_ifs
  · exact Subset.rfl
  · exact empty_subset _

theorem physicalReserve_measurable (cells : Cell → Component) (q : I) (draws : Cell → I) :
    MeasurableSet (physicalReserve cells q draws) :=
  MeasurableSet.iUnion (retainedCarrier_measurable cells q draws)

/-- The cached weighted Bernoulli sum is exactly the actual measure of the
retained union, including its assigned endpoints. -/
theorem physicalReserve_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : Cell → Component) (q : I) (draws : Cell → I)
    (hdisjoint : Pairwise (fun c d => Disjoint (cells c).carrier (cells d).carrier)) :
    μ.real (physicalReserve cells q draws) =
      reserveValue (fun c => μ.real (cells c).carrier) q draws := by
  unfold physicalReserve reserveValue
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro c _
    simp only [retainedCarrier, mark, indicator_apply, mem_Iic]
    split_ifs <;> simp
  · intro c d hcd
    exact (hdisjoint hcd).mono (retainedCarrier_subset cells q draws c)
      (retainedCarrier_subset cells q draws d)
  · exact retainedCarrier_measurable cells q draws

/-- Direct physical form of the row reserve-mass failure bound. -/
theorem physicalReserve_bad_probability (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : Cell → Component) (q : I) (eta : ℝ) (hq : 0 < (q : ℝ))
    (hdisjoint : Pairwise (fun c d => Disjoint (cells c).carrier (cells d).carrier))
    (hsmall : ∀ c, μ.real (cells c).carrier ≤ eta)
    (hnormalized : ∑ c, μ.real (cells c).carrier = 1) :
    labelLaw {draws | μ.real (physicalReserve cells q draws) < (q : ℝ) / 2 ∨
        3 * (q : ℝ) / 2 < μ.real (physicalReserve cells q draws)} ≤
      ENNReal.ofReal (4 * eta / (q : ℝ)) := by
  simp_rw [physicalReserve_mass μ cells q _ hdisjoint]
  exact badMass_probability _ q eta hq (fun _ => measureReal_nonneg) hsmall hnormalized

end EnvyFreeResearch.Full.UpperReserve
