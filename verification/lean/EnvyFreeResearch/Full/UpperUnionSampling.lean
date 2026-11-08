import EnvyFreeResearch.Full.UpperRecordedDomain
import EnvyFreeResearch.Full.UpperProbability

/-!
# Exact normalized sampling on a recorded finite union

The physical endpoint is the output of the cached-mass scan and ordinary-query
executor. Its normalized CDF equation is derived from the actual restricted
measure. An arbitrary measurable history-dependent response policy therefore
gives the exact normalized cutter law, with at most one Cut and all `n`
original-observer endpoint records.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperUnionSampling

open UpperRecordedDomain UpperCircularStage Chores

theorem positive_real_mass_ne_zero (μ : Measure ℝ) (U : Set ℝ)
    (hpos : 0 < μ.real U) : μ U ≠ 0 := by
  intro h
  simp [measureReal_def, h] at hpos

theorem normalized_cdf (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U : Set ℝ) (hpos : 0 < μ.real U) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ U) x = μ.real (U ∩ Iic x) / μ.real U := by
  let : IsProbabilityMeasure (ProbabilityTheory.cond μ U) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero μ U hpos)
  rw [cdf_eq_real, measureReal_def, cond_apply' measurableSet_Iic μ,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (μ.real U)⁻¹ * μ.real (U ∩ Iic x) = μ.real (U ∩ Iic x) / μ.real U
  ring

/-- The total sample executor retains a harmless default on an unreachable
positive-target failure. The following theorem proves that failure does not
occur for any draw in `(0,1]` and any admissible response policy. -/
def sampleExecution {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cs : List Component) (draw : I) : ℝ × History n :=
  (executeDomain policy history cutter cached ((draw : ℝ) * total) cs).getD (0, history)

/-- The deterministic cap includes every draw, including the null target zero
and the total default used for malformed inputs. -/
theorem sampleExecution_query_bound {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cs : List Component) (draw : I) :
    (sampleExecution policy history cutter cached total cs draw).2.length ≤
      history.length + n + 1 := by
  cases h : locate cached ((draw : ℝ) * total) cs with
  | none =>
    simp only [sampleExecution, executeDomain, h, Option.map_none, Option.getD_none]
    omega
  | some r =>
    simp only [sampleExecution, executeDomain, h, Option.map_some, Option.getD_some]
    exact executeRoute_query_bound policy history cutter cached _ r

theorem sampleExecution_cut_bound {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (cached : Component → ℝ) (total : ℝ)
    (cs : List Component) (draw : I) :
    ((sampleExecution policy history cutter cached total cs draw).2.map Prod.fst).countP isCut ≤
      (history.map Prod.fst).countP isCut + 1 := by
  cases h : locate cached ((draw : ℝ) * total) cs with
  | none =>
    simp only [sampleExecution, executeDomain, h, Option.map_none, Option.getD_none]
    omega
  | some r =>
    simp only [sampleExecution, executeDomain, h, Option.map_some, Option.getD_some]
    exact executeRoute_cut_bound policy history cutter cached _ r

theorem sampleExecution_unconditional_query_bound {n : ℕ}
    (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cs : List Component) :
    (∫⁻ draw,
      (((sampleExecution policy history cutter cached total cs draw).2.length - history.length : ℕ)
        : ℝ≥0∞) ∂(volume : Measure I)) ≤ (n + 1 : ℕ) := by
  calc
    _ ≤ ∫⁻ _draw : I, ((n + 1 : ℕ) : ℝ≥0∞) := by
      apply lintegral_mono
      intro draw
      have h := sampleExecution_query_bound policy history cutter cached total cs draw
      dsimp only
      exact_mod_cast (show (sampleExecution policy history cutter cached total cs draw).2.length -
        history.length ≤ n + 1 by omega)
    _ = _ := by simp

theorem sampleExecution_unconditional_cut_bound {n : ℕ}
    (policy : Policy n) (history : History n) (cutter : Fin n)
    (cached : Component → ℝ) (total : ℝ) (cs : List Component) :
    (∫⁻ draw,
      ((((sampleExecution policy history cutter cached total cs draw).2.map Prod.fst).countP isCut -
        (history.map Prod.fst).countP isCut : ℕ) : ℝ≥0∞) ∂(volume : Measure I)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _draw : I, (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro draw
      have h := sampleExecution_cut_bound policy history cutter cached total cs draw
      dsimp only
      exact_mod_cast (show ((sampleExecution policy history cutter cached total cs draw).2.map
        Prod.fst).countP isCut - (history.map Prod.fst).countP isCut ≤ 1 by omega)
    _ = _ := by simp

theorem sampleExecution_spec {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile cost) policy)
    (history : History n) (cutter : Fin n) (cached : Component → ℝ) (cs : List Component)
    (hordered : Ordered cs) (hdisjoint : DisjointComponents cs)
    (hcache : ∀ c ∈ cs, cached c = mass (cost cutter) c)
    (hpos : 0 < (cost cutter).real (domain cs))
    (draw : I) (hdraw : 0 < (draw : ℝ)) :
    let result := sampleExecution policy history cutter cached ((cost cutter).real (domain cs)) cs draw
    result.1 ∈ Icc (0 : ℝ) 1 ∧
      cdf (ProbabilityTheory.cond (cost cutter) (domain cs)) result.1 = (draw : ℝ) ∧
      result.2.length ≤ history.length + n + 1 ∧
      (result.2.map Prod.fst).countP isCut ≤ (history.map Prod.fst).countP isCut + 1 := by
  obtain ⟨endpoint, returnedHistory, hexec, hloc, hprefix, hqueries, hcuts⟩ :=
    ordinary_union_cut cost policy hpolicy history cutter cached
      ((draw : ℝ) * (cost cutter).real (domain cs)) cs hordered hdisjoint hcache
      (mul_pos hdraw hpos) (by nlinarith [draw.property.2])
  simp only [sampleExecution, hexec, Option.getD_some]
  refine ⟨hloc, ?_, hqueries, hcuts⟩
  rw [normalized_cdf (cost cutter) (domain cs) hpos endpoint, hprefix]
  exact mul_div_cancel_right₀ (draw : ℝ) hpos.ne'

/-- A unit-interval draw followed by the actual ordinary-domain Cut has the
normalized restricted cutter law under every admissible policy whose realized
endpoint map is measurable. No fixed or extremal root convention is required. -/
theorem sampleExecution_law {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile cost) policy)
    (history : History n) (cutter : Fin n) (cached : Component → ℝ) (cs : List Component)
    (hordered : Ordered cs) (hdisjoint : DisjointComponents cs)
    (hcache : ∀ c ∈ cs, cached c = mass (cost cutter) c)
    (hpos : 0 < (cost cutter).real (domain cs))
    (hmeas : Measurable (fun draw =>
      (sampleExecution policy history cutter cached ((cost cutter).real (domain cs)) cs draw).1)) :
    (volume : Measure I).map (fun draw =>
      (sampleExecution policy history cutter cached ((cost cutter).real (domain cs)) cs draw).1) =
        ProbabilityTheory.cond (cost cutter) (domain cs) := by
  let : IsProbabilityMeasure (ProbabilityTheory.cond (cost cutter) (domain cs)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero (cost cutter) (domain cs) hpos)
  apply UpperProbability.arbitrary_legal_root_map _ _ hmeas
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with draw hdraw
  have hd : 0 < (draw : ℝ) := by
    have hdne : (draw : ℝ) ≠ 0 := fun h => hdraw (Subtype.ext h)
    exact lt_of_le_of_ne draw.property.1 hdne.symm
  exact (sampleExecution_spec cost policy hpolicy history cutter cached cs
    hordered hdisjoint hcache hpos draw hd).2.1

end EnvyFreeResearch.Full.UpperUnionSampling
