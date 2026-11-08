import EnvyFreeResearch.Full.UpperDomainDifferenceHistory

/-!
# Actual Cut histories preserve the cache invariant

A correctly recorded input domain stays correctly recorded after the two
ordinary endpoint executions and literal correction removal. The proof tracks
actual appended answers, including the no-query cached-boundary branch.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperEndpointCache

open UpperRecordedDomain UpperDomainDifference UpperCircularStage UpperUnionSampling
  UpperUnionCircular UpperCircular IntervalOracle Chores

abbrev Circle := UpperCircular.Circle

variable {n : ℕ}

def Truthful (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (history : History n) : Prop :=
  ∀ entry ∈ history, ValidReply (measureProfile μ) entry.1 entry.2

def RecordedHistory (cs : List Component) (history : History n) : Prop :=
  ∀ i p, Recorded cs p → ∃ answer, (IntervalOracle.Query.eval i 0 p, answer) ∈ history

theorem recordedHistory_mono (cs : List Component) {old new : History n}
    (h : RecordedHistory cs old) (hextend : old ⊆ new) : RecordedHistory cs new := by
  intro i p hp
  obtain ⟨answer, ha⟩ := h i p hp
  exact ⟨answer, hextend ha⟩

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)

include hpolicy

theorem executeRoute_history (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (target : ℝ) (cs : List Component)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cs history)
    (hcache : ∀ c ∈ cs, cache c = mass (μ cutter) c)
    (r : Route Component) (hsplit : cs = r.before ++ r.cell :: r.after)
    (hlow : sumValues cache r.before ≤ target)
    (hhigh : target ≤ sumValues cache r.before + cache r.cell) :
    let result := executeRoute policy history cutter cache target r
    Truthful μ result.2 ∧ history ⊆ result.2 ∧
      ∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 result.1, answer) ∈ result.2 := by
  have hcell : cache r.cell = mass (μ cutter) r.cell := hcache r.cell (by rw [hsplit]; simp)
  have hres0 : 0 ≤ target - sumValues cache r.before := by linarith
  have hres : target - sumValues cache r.before ≤ mass (μ cutter) r.cell := by
    rw [← hcell]
    linarith
  by_cases hb : target - sumValues cache r.before = cache r.cell
  · simp only [executeRoute, hb, ite_true]
    refine ⟨htruth, fun _ h => h, ?_⟩
    intro i
    exact hrecorded i r.cell.right ⟨r.cell, by rw [hsplit]; simp, Or.inr rfl⟩
  · let query := componentQuery cutter r.cell (target - sumValues cache r.before)
    have hq := componentQuery_legal μ cutter r.cell hres0 hres
    have hv := hpolicy history query hq
    have hx : policy history query ∈ Icc (0 : ℝ) 1 :=
      ⟨r.cell.left_nonneg.trans hv.1.1, hv.1.2.trans r.cell.right_le_one⟩
    obtain ⟨fresh, hrun, hproj, hfresh⟩ := executeQueries_newReplies (measureProfile μ) policy hpolicy
      (recordings n (policy history query)) (history ++ [(query, policy history query)])
      (UpperCircularStage.recordings_legal (measureProfile μ) _ hx)
    change Truthful μ (executeRoute policy history cutter cache target r).2 ∧ _
    simp only [executeRoute, hb, ite_false]
    change Truthful μ (executeQueries policy (recordings n (policy history query))
        (history ++ [(query, policy history query)])) ∧ _
    rw [hrun]
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      rcases List.mem_append.mp hentry with hentry | hentry
      · rcases List.mem_append.mp hentry with hentry | hentry
        · exact htruth entry hentry
        · have he : entry = (query, policy history query) := by simpa using hentry
          subst entry
          exact hv
      · exact hfresh entry hentry
    · intro entry hentry
      exact List.mem_append_left _ (List.mem_append_left _ hentry)
    · intro i
      have hi : IntervalOracle.Query.eval i 0 (policy history query) ∈ fresh.map Prod.fst := by
        rw [hproj]
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hi
      refine ⟨entry.2, List.mem_append_right _ ?_⟩
      have heq : (IntervalOracle.Query.eval i 0 (policy history query), entry.2) = entry :=
        Prod.ext he.symm rfl
      rwa [heq]

theorem sampleExecution_history (history : History n) (cutter : Fin n)
    (cache : Component → ℝ) (cs : List Component) (hdisjoint : DisjointComponents cs)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cs history)
    (hcache : ∀ c ∈ cs, cache c = mass (μ cutter) c)
    (hpositive : 0 < (μ cutter).real (domain cs)) (draw : I) (hdraw : 0 < (draw : ℝ)) :
    let result := sampleExecution policy history cutter cache ((μ cutter).real (domain cs)) cs draw
    Truthful μ result.2 ∧ history ⊆ result.2 ∧
      ∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 result.1, answer) ∈ result.2 := by
  have hsum : (μ cutter).real (domain cs) = sumValues cache cs := by
    rw [domain_mass_sum (μ cutter) cs hdisjoint, cached_sum_eq (μ cutter) cs cache hcache]
  obtain ⟨r, hroute, hsplit, hlow, hhigh⟩ := locate_spec cache cs
    ((draw : ℝ) * (μ cutter).real (domain cs)) (mul_pos hdraw hpositive)
    (by rw [← hsum]; exact mul_le_of_le_one_left hpositive.le draw.property.2)
  simp only [sampleExecution, executeDomain, hroute, Option.map_some, Option.getD_some]
  exact executeRoute_history μ policy hpolicy history cutter cache _ cs htruth hrecorded hcache
    r hsplit hlow.le hhigh

/-- The final history contains both endpoint records, every old answer, and
only truthful new answers. Both Cuts may use arbitrary legal history-dependent
root choices, including distinct replies to repeated requests. -/
theorem circular_history (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (cs : List Component) (hdisjoint : DisjointComponents cs)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cs history)
    (hcache : ∀ c ∈ cs, cache c = mass (μ cutter) c)
    (hpositive : 0 < (μ cutter).real (domain cs)) (amount : I) (start : Circle) :
    let first := firstRun policy history cutter cache ((μ cutter).real (domain cs)) cs start
    let last := secondRun policy history cutter cache ((μ cutter).real (domain cs)) cs amount start
    Truthful μ last.2 ∧ history ⊆ last.2 ∧
      (∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 first.1, answer) ∈ last.2) ∧
      (∀ i, ∃ answer, (IntervalOracle.Query.eval i 0 last.1, answer) ∈ last.2) := by
  have hfirst := sampleExecution_history μ policy hpolicy history cutter cache cs hdisjoint
    htruth hrecorded hcache hpositive (value start) (UpperPhysical.value_positive start)
  have hsecond := sampleExecution_history μ policy hpolicy _ cutter cache cs hdisjoint
    hfirst.1 (recordedHistory_mono cs hrecorded hfirst.2.1) hcache hpositive
    (value (start + project amount)) (UpperPhysical.value_positive _)
  refine ⟨hsecond.1, fun _ h => hsecond.2.1 (hfirst.2.1 h), ?_, hsecond.2.2⟩
  intro i
  obtain ⟨answer, ha⟩ := hfirst.2.2 i
  exact ⟨answer, hsecond.2.1 ha⟩

/-- Literal endpoint refinement and correction removal preserve a truthful,
fully recorded cache for every original observer, not only the active cutter. -/
theorem removed_cache_correct (history : History n) (cutter : Fin n) (cache : Component → ℝ)
    (cs : List Component) (hdisjoint : DisjointComponents cs)
    (htruth : Truthful μ history) (hrecorded : RecordedHistory cs history)
    (hcache : ∀ c ∈ cs, cache c = mass (μ cutter) c)
    (hpositive : 0 < (μ cutter).real (domain cs)) (amount : I) (start : Circle) :
    let descriptor := recordedCorrection policy history cutter cache ((μ cutter).real (domain cs)) cs amount start
    let finalHistory := (secondRun policy history cutter cache ((μ cutter).real (domain cs)) cs amount start).2
    let remaining := applyCorrection cs descriptor
    Truthful μ finalHistory ∧ RecordedHistory remaining finalHistory ∧
      PrefixCorrect μ (historyPrefix finalHistory) remaining := by
  have h := circular_history μ policy hpolicy history cutter cache cs hdisjoint htruth hrecorded
    hcache hpositive amount start
  dsimp only
  have hr : RecordedHistory
      (applyCorrection cs (recordedCorrection policy history cutter cache ((μ cutter).real (domain cs)) cs amount start))
      (secondRun policy history cutter cache ((μ cutter).real (domain cs)) cs amount start).2 := by
    intro i p hp
    rcases removeCorrection_recorded cs amount start _ _ hp with rfl | rfl | hp
    · exact h.2.2.1 i
    · exact h.2.2.2 i
    · obtain ⟨answer, ha⟩ := hrecorded i p hp
      exact ⟨answer, h.2.1 ha⟩
  exact ⟨h.1, hr, historyPrefix_prefixCorrect μ _ _ h.1 hr⟩

end EnvyFreeResearch.Full.UpperEndpointCache
