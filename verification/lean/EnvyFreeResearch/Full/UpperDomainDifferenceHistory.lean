import EnvyFreeResearch.Full.UpperDomainDifferenceRecorded

/-! Deterministic Borel access to actual recorded prefix answers. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain UpperCircularStage UpperStageMeasurable ProtocolMeasurable
  Chores IntervalOracle

variable {n : ℕ}

def prefixCode : UpperCircularStage.Query n → Bool × Fin n × ℝ × ℝ
  | .eval i a b => (true, i, a, b)
  | .cut i a b _ => (false, i, a, b)

theorem prefixCode_measurable : Measurable (prefixCode (n := n)) := by
  apply measurable_query_cases
  · exact measurable_const.prodMk measurable_id
  · exact measurable_const.prodMk (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))

def prefixMatches (i : Fin n) (p : ℝ) (q : UpperCircularStage.Query n) : Prop :=
  prefixCode q = (true, i, 0, p)

theorem prefixMatches_iff (i : Fin n) (p : ℝ) (q : UpperCircularStage.Query n) :
    prefixMatches i p q ↔ q = IntervalOracle.Query.eval i 0 p := by
  cases q <;> simp [prefixMatches, prefixCode]

def prefixUpdate (i : Fin n) (p : ℝ) (old : ℝ) (entry : UpperCircularStage.Query n × ℝ) : ℝ :=
  if prefixMatches i p entry.1 then entry.2 else old

/-- Latest matching Eval answer, or zero if none has been recorded. -/
def historyPrefix (history : History n) (i : Fin n) (p : ℝ) : ℝ :=
  history.foldl (prefixUpdate i p) 0

theorem prefix_fold_preserves (i : Fin n) (p v : ℝ) (history : History n)
    (hvalid : ∀ entry ∈ history, prefixMatches i p entry.1 → entry.2 = v) :
    history.foldl (prefixUpdate i p) v = v := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
    have he : prefixUpdate i p v entry = v := by
      unfold prefixUpdate
      split_ifs with h
      · exact hvalid entry (by simp) h
      · rfl
    rw [List.foldl_cons, he]
    exact ih (fun e he => hvalid e (by simp [he]))

theorem prefix_fold_correct (i : Fin n) (p v seed : ℝ) (history : History n)
    (hvalid : ∀ entry ∈ history, prefixMatches i p entry.1 → entry.2 = v)
    (hfound : ∃ entry ∈ history, prefixMatches i p entry.1) :
    history.foldl (prefixUpdate i p) seed = v := by
  induction history generalizing seed with
  | nil => simp at hfound
  | cons entry rest ih =>
    have hrest : ∀ e ∈ rest, prefixMatches i p e.1 → e.2 = v :=
      fun e he => hvalid e (by simp [he])
    by_cases h : prefixMatches i p entry.1
    · rw [List.foldl_cons, prefixUpdate, ite_eq_left h, hvalid entry (by simp) h]
      exact prefix_fold_preserves i p v rest hrest
    · rw [List.foldl_cons, prefixUpdate, ite_eq_right h]
      apply ih seed hrest
      obtain ⟨e, he, hp⟩ := hfound
      rcases List.mem_cons.mp he with rfl | he
      · exact (h hp).elim
      · exact ⟨e, he, hp⟩

theorem historyPrefix_correct (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (history : History n)
    (hvalid : ∀ entry ∈ history, ValidReply (measureProfile μ) entry.1 entry.2)
    (i : Fin n) (p : ℝ)
    (hfound : ∃ answer, (IntervalOracle.Query.eval i 0 p, answer) ∈ history) :
    historyPrefix history i p = (μ i).real (Ioc 0 p) := by
  apply prefix_fold_correct
  · intro entry hentry hmatch
    have hv := hvalid entry hentry
    rw [prefixMatches_iff] at hmatch
    rw [hmatch] at hv
    change entry.2 = prefixCost (μ i) 0 p - prefixCost (μ i) 0 0 at hv
    rw [prefixCost_self, sub_zero] at hv
    exact hv.trans (prefix_Ioc_eq_prefixCost (μ i) p).symm
  · obtain ⟨answer, hanswer⟩ := hfound
    exact ⟨(_, answer), hanswer, (prefixMatches_iff i p _).mpr rfl⟩

/-- Recorded endpoints and truthful answered entries yield the required cache
invariant for the actual deterministic lookup. -/
theorem historyPrefix_prefixCorrect (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (history : History n) (cs : List Component)
    (hvalid : ∀ entry ∈ history, ValidReply (measureProfile μ) entry.1 entry.2)
    (hrecorded : ∀ i p, Recorded cs p →
      ∃ answer, (IntervalOracle.Query.eval i 0 p, answer) ∈ history) :
    PrefixCorrect μ (historyPrefix history) cs :=
  fun i p hp => historyPrefix_correct μ history hvalid i p (hrecorded i p hp)

/-- The appended all-observer recording determines the lookup even if the
previous history was arbitrary. The last recorded matching answer wins. -/
theorem historyPrefix_after_recordings (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (history : History n) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    historyPrefix (executeQueries policy (recordings n p) history) i p =
      (μ i).real (Ioc 0 p) := by
  obtain ⟨fresh, hrun, hproj, hvalid⟩ := executeQueries_newReplies (measureProfile μ) policy hpolicy
    (recordings n p) history (recordings_legal (measureProfile μ) p hp)
  rw [hrun, historyPrefix, List.foldl_append]
  apply prefix_fold_correct
  · intro entry hentry hmatch
    have hv := hvalid entry hentry
    rw [prefixMatches_iff] at hmatch
    rw [hmatch] at hv
    change entry.2 = prefixCost (μ i) 0 p - prefixCost (μ i) 0 0 at hv
    rw [prefixCost_self, sub_zero] at hv
    exact hv.trans (prefix_Ioc_eq_prefixCost (μ i) p).symm
  · have hq : IntervalOracle.Query.eval i 0 p ∈ fresh.map Prod.fst := by
      rw [hproj]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hq
    exact ⟨entry, hentry, (prefixMatches_iff i p entry.1).mpr heq⟩

variable {X : Type*} [MeasurableSpace X]

theorem historyPrefix_measurable (history : X → History n) (i : X → Fin n) (p : X → ℝ)
    (hhistory : Measurable history) (hi : Measurable i) (hp : Measurable p) :
    Measurable (fun z => historyPrefix (history z) (i z) (p z)) := by
  apply list_foldl_measurable (fun z old entry => prefixUpdate (i z) (p z) old entry)
    (fun _ => (0 : ℝ)) history
  · have hq : Measurable (fun z : X × ℝ × (UpperCircularStage.Query n × ℝ) =>
        prefixCode z.2.2.1) := prefixCode_measurable.comp
          (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have ht : Measurable (fun z : X × ℝ × (UpperCircularStage.Query n × ℝ) =>
        (true, i z.1, (0 : ℝ), p z.1)) :=
      measurable_const.prodMk ((hi.comp measurable_fst).prodMk
        (measurable_const.prodMk (hp.comp measurable_fst)))
    exact (measurable_snd.comp (measurable_snd.comp measurable_snd)).ite
      (measurableSet_eq_fun hq ht) (measurable_fst.comp measurable_snd)
  · exact measurable_const
  · exact hhistory

/-- Cache subtraction on actual history coordinates is Borel. -/
theorem history_cached_measurable (history : X → History n) (c : X → Component)
    (hhistory : Measurable history) (hc : Measurable c) (i : Fin n) :
    Measurable (fun z => cached (historyPrefix (history z)) i (c z)) :=
  (historyPrefix_measurable history (fun _ => i) (fun z => (c z).right)
    hhistory measurable_const (component_right_measurable.comp hc)).sub
  (historyPrefix_measurable history (fun _ => i) (fun z => (c z).left)
    hhistory measurable_const (component_left_measurable.comp hc))

end EnvyFreeResearch.Full.UpperDomainDifference
