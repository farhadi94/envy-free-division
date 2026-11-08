import EnvyFreeResearch.Full.UpperEndpointCache
import EnvyFreeResearch.Full.UpperFreshSamples

/-!
# Sampling endpoint records, including the zero target

The literal endpoint and cache guarantees hold on every draw in `[0,1]`,
including the probability-zero target zero. A finite run records every output
endpoint in the final history while preserving all earlier answers.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperSamplingRecords

open UpperRecordedDomain UpperDomainDifference UpperEndpointCache UpperCircularStage
  UpperUnionSampling IntervalOracle Chores

theorem locate_nonnegative {α : Type*} (v : α → ℝ) (cs : List α) (hne : cs ≠ [])
    (hv : ∀ c ∈ cs, 0 ≤ v c) (target : ℝ) (htarget : 0 ≤ target) (hbound : target ≤ sumValues v cs) :
    ∃ r, locate v target cs = some r ∧ cs = r.before ++ r.cell :: r.after ∧
      sumValues v r.before ≤ target ∧ target ≤ sumValues v r.before + v r.cell := by
  by_cases hp : 0 < target
  · obtain ⟨r, hr, hs, hl, hu⟩ := locate_spec v cs target hp hbound
    exact ⟨r, hr, hs, hl.le, hu⟩
  · have hz : target = 0 := le_antisymm (le_of_not_gt hp) htarget
    subst target
    cases cs with
    | nil => exact (hne rfl).elim
    | cons c cs =>
      have hc := hv c (by simp)
      exact ⟨⟨[], c, cs⟩, by simp [locate, hc], rfl, le_rfl, by simpa using hc⟩

variable {n : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)

include hpolicy

theorem executeRoute_endpoint_unit (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (target : ℝ) (r : Route Component)
    (hcache : cache r.cell = mass (μ cutter) r.cell)
    (hlow : sumValues cache r.before ≤ target)
    (hhigh : target ≤ sumValues cache r.before + cache r.cell) :
    (executeRoute policy history cutter cache target r).1 ∈ Icc (0 : ℝ) 1 := by
  have hres0 : 0 ≤ target - sumValues cache r.before := sub_nonneg.mpr hlow
  have hres : target - sumValues cache r.before ≤ mass (μ cutter) r.cell := by
    rw [← hcache]
    linarith
  by_cases hb : target - sumValues cache r.before = cache r.cell
  · simp only [executeRoute, hb, ite_true]
    exact ⟨r.cell.left_nonneg.trans r.cell.left_le_right, r.cell.right_le_one⟩
  · have hv := hpolicy history _ (componentQuery_legal μ cutter r.cell hres0 hres)
    simp only [executeRoute, hb, ite_false]
    exact ⟨r.cell.left_nonneg.trans hv.1.1, hv.1.2.trans r.cell.right_le_one⟩

/-- Every actual sample endpoint lies in the resource and is fully recorded;
no almost-everywhere exception is needed for the geometric grid adapter. -/
theorem sampleExecution_all_records (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (cs : List Component) (hdisjoint : DisjointComponents cs)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cs history)
    (hcache : ∀ c ∈ cs, cache c = mass (μ cutter) c)
    (hpositive : 0 < (μ cutter).real (domain cs)) (draw : I) :
    let result := sampleExecution policy history cutter cache ((μ cutter).real (domain cs)) cs draw
    result.1 ∈ Icc (0 : ℝ) 1 ∧ Truthful μ result.2 ∧ history ⊆ result.2 ∧
      ∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 result.1, answer) ∈ result.2 := by
  have hsum : (μ cutter).real (domain cs) = sumValues cache cs := by
    rw [domain_mass_sum (μ cutter) cs hdisjoint, cached_sum_eq (μ cutter) cs cache hcache]
  have hne : cs ≠ [] := by intro h; simp [h, domain] at hpositive
  obtain ⟨r, hroute, hsplit, hlow, hhigh⟩ := locate_nonnegative cache cs hne
    (fun c hc => by rw [hcache c hc]; exact measureReal_nonneg)
    ((draw : ℝ) * (μ cutter).real (domain cs)) (mul_nonneg draw.property.1 hpositive.le)
    (by rw [← hsum]; exact mul_le_of_le_one_left hpositive.le draw.property.2)
  simp only [sampleExecution, executeDomain, hroute, Option.map_some, Option.getD_some]
  exact ⟨executeRoute_endpoint_unit μ policy hpolicy history cutter cache _ r
      (hcache r.cell (by rw [hsplit]; simp)) hlow hhigh,
    executeRoute_history μ policy hpolicy history cutter cache _ cs htruth hrecorded hcache
      r hsplit hlow hhigh⟩

end EnvyFreeResearch.Full.UpperSamplingRecords
