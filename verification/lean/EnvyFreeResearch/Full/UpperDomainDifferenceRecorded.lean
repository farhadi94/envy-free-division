import EnvyFreeResearch.Full.UpperDomainDifferenceDynamic
import EnvyFreeResearch.Full.UpperUnionCircular

/-! The actual appended endpoint recordings and physical-stage adapter. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain UpperCircularStage UpperStageMeasurable UpperUnionCircular
  Chores IntervalOracle

variable {n : ℕ}

theorem executeQueries_newReplies (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (queries : List (UpperCircularStage.Query n))
    (history : History n) (hlegal : ∀ q ∈ queries, Legal P q) :
    ∃ fresh : History n, executeQueries policy queries history = history ++ fresh ∧
      fresh.map Prod.fst = queries ∧ ∀ entry ∈ fresh, ValidReply P entry.1 entry.2 := by
  induction queries generalizing history with
  | nil => exact ⟨[], by simp [executeQueries], rfl, by simp⟩
  | cons q queries ih =>
    obtain ⟨fresh, hrun, hproj, hvalid⟩ := ih (history ++ [(q, policy history q)])
      (fun r hr => hlegal r (by simp [hr]))
    refine ⟨(q, policy history q) :: fresh, ?_, ?_, ?_⟩
    · simpa [executeQueries, List.append_assoc] using hrun
    · simp [hproj]
    · intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | hentry
      · exact hpolicy history q (hlegal q (by simp))
      · exact hvalid entry hentry

/-- Every original observer's correct prefix occurs in the actual appended
recording block, independently of the earlier history and cut choices. -/
theorem recordings_prefix_values (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (history : History n) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∃ fresh : History n,
      executeQueries policy (recordings n p) history = history ++ fresh ∧
      ∀ i : Fin n, ∃ answer,
        (IntervalOracle.Query.eval i 0 p, answer) ∈ fresh ∧ answer = (μ i).real (Ioc 0 p) := by
  obtain ⟨fresh, hrun, hproj, hvalid⟩ := executeQueries_newReplies (measureProfile μ) policy hpolicy
    (recordings n p) history (recordings_legal (measureProfile μ) p hp)
  refine ⟨fresh, hrun, ?_⟩
  intro i
  have hq : IntervalOracle.Query.eval i 0 p ∈ fresh.map Prod.fst := by
    rw [hproj]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hq
  have hv := hvalid entry hentry
  rw [heq] at hv
  change entry.2 = prefixCost (μ i) 0 p - prefixCost (μ i) 0 0 at hv
  rw [prefixCost_self, sub_zero] at hv
  refine ⟨entry.2, ?_, hv.trans (prefix_Ioc_eq_prefixCost (μ i) p).symm⟩
  have hh : (IntervalOracle.Query.eval i 0 p, entry.2) = entry := by
    apply Prod.ext
    · exact heq.symm
    · rfl
  rw [hh]
  exact hentry

def recordedCorrection (policy : Policy n) (history : History n) (cutter : Fin n)
    (values : Component → ℝ) (total : ℝ) (cs : List Component) (amount : I)
    (start : UpperCircular.Circle) : Correction where
  amount := amount
  start := start
  first := (firstRun policy history cutter values total cs start).1
  last := (secondRun policy history cutter values total cs amount start).1

/-- The descriptor deletes the literal piece returned by the actual two-Cut
stage, including its endpoint-owned complement in the wrap case. -/
theorem remove_recorded_domain (policy : Policy n) (history : History n) (cutter : Fin n)
    (values : Component → ℝ) (total : ℝ) (cs : List Component) (amount : I)
    (start : UpperCircular.Circle) :
    domain (applyCorrection cs (recordedCorrection policy history cutter values total cs amount start)) =
      domain cs \ UpperUnionCircular.piece policy history cutter values total cs amount start :=
  removeCorrection_domain cs amount start _ _

theorem recordedCorrection_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (values : Component → ℝ) (total : ℝ)
    (cs : List Component) (amount : I) :
    Measurable (recordedCorrection policy history cutter values total cs amount) := by
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (measurable_id.prodMk
    ((measurable_fst.comp (firstRun_measurable policy hpolicy history cutter values total cs)).prodMk
      (measurable_fst.comp (secondRun_measurable policy hpolicy history cutter values total cs amount))))

theorem remove_recorded_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (history : History n) (cutter : Fin n) (values : Component → ℝ) (total : ℝ)
    (cs : List Component) (amount : I) :
    Measurable (fun start => applyCorrection cs
      (recordedCorrection policy history cutter values total cs amount start)) :=
  applyCorrection_measurable _ _ measurable_const
    (recordedCorrection_measurable policy hpolicy history cutter values total cs amount)

end EnvyFreeResearch.Full.UpperDomainDifference
