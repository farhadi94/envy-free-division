import EnvyFreeResearch.Full.ChoresAdaptive

/-!
# Recording a fresh physical prefix with ordinary adaptive queries

The deterministic protocol issues one ordinary Cut and then one Eval for each
other enclosing observer. Its next action depends only on the answered
history. The trimmer's cost is recovered from the target equation, so exactly
`n` queries record all `n` costs, even for arbitrary history-dependent roots.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores

open Set OracleProtocol IntervalOracle

structure EndpointRecord (n : ℕ) where
  point : ℝ
  value : Fin n → ℝ

/-- The trimmer is omitted because the Cut already determines that value. -/
def recordingObservers {n : ℕ} (i : Fin n) : List (Fin n) := by
  classical
  exact (Finset.univ.erase i).toList

lemma recordingObservers_length {n : ℕ} (i : Fin n) :
    (recordingObservers i).length = n - 1 := by simp [recordingObservers]

lemma mem_recordingObservers {n : ℕ} (i j : Fin n) :
    j ∈ recordingObservers i ↔ j ≠ i := by simp [recordingObservers]

/-- A value is read only from an actual answered Eval carrying that observer. -/
def readRecorded {n : ℕ} : History (Query (Fin n)) ℝ → Fin n → ℝ
  | [], _ => 0
  | (.eval j _ _, r) :: rest, i => if i = j then r else readRecorded rest i
  | (.cut _ _ _ _, _) :: rest, i => readRecorded rest i

def completedRecord {n : ℕ} (i : Fin n) (t x : ℝ)
    (evals : History (Query (Fin n)) ℝ) : EndpointRecord n :=
  ⟨x, Function.update (readRecorded evals) i t⟩

/-- This protocol is independent of the cost profile and reply policy. -/
def endpointProtocol {n : ℕ} (i : Fin n) (a b t : ℝ) :
    Protocol Unit (Query (Fin n)) ℝ (EndpointRecord n) :=
  fun _ history => match history with
  | [] => .ask (.cut i a b t)
  | (_, x) :: evals =>
    match (recordingObservers i).drop evals.length with
    | [] => .returned (completedRecord i t x evals)
    | j :: _ => .ask (.eval j a x)

/-- Sequential history threading for the fixed list of recording Evals. -/
def evalBatch {n : ℕ} (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (a x : ℝ) : List (Fin n) → History (Query (Fin n)) ℝ → History (Query (Fin n)) ℝ
  | [], _ => []
  | j :: rest, history =>
    let q := Query.eval j a x
    let r := AdaptiveOracle.answer oracle history q
    (q, r) :: evalBatch oracle a x rest (history ++ [(q, r)])

lemma evalBatch_length {n : ℕ} (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (a x : ℝ) (observers : List (Fin n)) (history : History (Query (Fin n)) ℝ) :
    (evalBatch oracle a x observers history).length = observers.length := by
  induction observers generalizing history with
  | nil => rfl
  | cons j rest ih => simp only [evalBatch, List.length_cons, ih]

lemma evalBatch_no_cuts {n : ℕ} (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (a x : ℝ) (observers : List (Fin n)) (history : History (Query (Fin n)) ℝ) :
    (evalBatch oracle a x observers history).countP (fun qr => isCutQuery qr.1) = 0 := by
  induction observers generalizing history with
  | nil => rfl
  | cons j rest ih =>
    simp only [evalBatch, List.countP_cons, isCutQuery]
    exact ih _

/-- Each recorded observer value comes from its actual legal Eval reply. -/
lemma evalBatch_values {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (a x : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hx : x ≤ 1)
    (observers : List (Fin n)) (history : History (Query (Fin n)) ℝ) :
    ∀ j ∈ observers, readRecorded (evalBatch oracle a x observers history) j =
      P.cumulative j x - P.cumulative j a := by
  induction observers generalizing history with
  | nil => simp
  | cons k rest ih =>
    intro j hj
    have hreply := (AdaptiveOracle.answer_spec P oracle hpolicy history (.eval k a x)
      ⟨ha, hax, hx⟩).2
    by_cases hjk : j = k
    · subst j
      simpa only [evalBatch, readRecorded, ite_true, ValidReply] using hreply
    · simp only [evalBatch, readRecorded, ite_eq_right hjk]
      apply ih
      exact (List.mem_cons.mp hj).resolve_left hjk

/-- The list executor is proved to be the exact trace of the fixed next-action
protocol, starting after any already answered recording prefix. -/
lemma endpoint_tail_trace {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (i : Fin n) (a b t x : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hx : x ≤ 1)
    (remaining : List (Fin n)) (done : History (Query (Fin n)) ℝ)
    (hremaining : (recordingObservers i).drop done.length = remaining) :
    AdaptiveOracle.run (endpointProtocol i a b t) oracle () remaining.length
      ((.cut i a b t, x) :: done) =
      ⟨evalBatch oracle a x remaining ((.cut i a b t, x) :: done),
        .returned (completedRecord i t x
          (done ++ evalBatch oracle a x remaining ((.cut i a b t, x) :: done)))⟩ := by
  induction remaining generalizing done with
  | nil =>
    have hnext : endpointProtocol i a b t () ((.cut i a b t, x) :: done) =
        .returned (completedRecord i t x done) := by simp [endpointProtocol, hremaining]
    simpa [evalBatch] using AdaptiveOracle.run_returned (endpointProtocol i a b t) oracle () 0 _ _ hnext
  | cons j rest ih =>
    let q := Query.eval j a x
    let r := AdaptiveOracle.answer oracle ((.cut i a b t, x) :: done) q
    have hnext : endpointProtocol i a b t () ((.cut i a b t, x) :: done) = .ask q := by
      simp [endpointProtocol, hremaining, q]
    have hreply : oracle ((.cut i a b t, x) :: done) q = some r :=
      (AdaptiveOracle.answer_spec P oracle hpolicy _ q ⟨ha, hax, hx⟩).1
    rw [List.length_cons, AdaptiveOracle.run_succ_some _ _ _ _ _ _ _ hnext hreply]
    have hdrop : (recordingObservers i).drop (done ++ [(q, r)]).length = rest := by
      rw [List.length_append, List.length_singleton, ← List.drop_drop, hremaining]
      rfl
    have htail := ih (done ++ [(q, r)]) hdrop
    simp only [List.cons_append] at *
    rw [htail]
    simp [evalBatch, q, r, List.append_assoc]

/-- Exact physical query count and all-observer endpoint recording for every
legal Cut target and every full-history legal reply policy. -/
theorem endpoint_protocol_correct {n : ℕ} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (i : Fin n) (a b t : ℝ) (hlegal : Legal P (.cut i a b t)) :
    ∃ record : EndpointRecord n,
      (AdaptiveOracle.run (endpointProtocol i a b t) oracle () n []).stop = .returned record ∧
      (AdaptiveOracle.run (endpointProtocol i a b t) oracle () n []).answered.length = n ∧
      (AdaptiveOracle.run (endpointProtocol i a b t) oracle () n []).answered.countP
        (fun qr => isCutQuery qr.1) = 1 ∧
      record.point ∈ Icc a b ∧
      (∀ j, record.value j = P.cumulative j record.point - P.cumulative j a) ∧
      record.value i = t := by
  let q := Query.cut i a b t
  let x := AdaptiveOracle.answer oracle [] q
  obtain ⟨hanswer, hroot⟩ := AdaptiveOracle.answer_spec P oracle hpolicy [] q hlegal
  have hx : x ∈ Icc a b := hroot.1
  let evals := evalBatch oracle a x (recordingObservers i) [(q, x)]
  let record := completedRecord i t x evals
  have hn : (recordingObservers i).length + 1 = n := by
    rw [recordingObservers_length]
    have := i.isLt
    omega
  have hnext : endpointProtocol i a b t () [] = .ask q := rfl
  have htail := endpoint_tail_trace P oracle hpolicy i a b t x hlegal.1 hx.1
    (hx.2.trans hlegal.2.2.1) (recordingObservers i) [] (by simp)
  have hrun : AdaptiveOracle.run (endpointProtocol i a b t) oracle () n [] =
      ⟨(q, x) :: evals, .returned record⟩ := by
    have hstep := AdaptiveOracle.run_succ_some (endpointProtocol i a b t) oracle ()
      (recordingObservers i).length [] q x hnext hanswer
    rw [hn] at hstep
    rw [hstep]
    simpa [record, evals, q] using congrArg
      (fun z : Execution (Query (Fin n)) ℝ (EndpointRecord n) =>
        ({ answered := (q, x) :: z.answered, stop := z.stop } : Execution _ _ _)) htail
  refine ⟨record, ?_, ?_, ?_, hx, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]
    simp only [List.length_cons, evals, evalBatch_length]
    exact hn
  · rw [hrun]
    simp only [List.countP_cons, q, isCutQuery]
    change (evalBatch oracle a x (recordingObservers i) [(q, x)]).countP (fun qr => isCutQuery qr.1) + 1 = 1
    rw [evalBatch_no_cuts]
  · intro j
    by_cases hji : j = i
    · subst j
      have heq : P.cumulative i x = P.cumulative i a + t := hroot.2
      change Function.update (readRecorded evals) i t i = P.cumulative i x - P.cumulative i a
      rw [Function.update_self]
      linarith only [heq]
    · change Function.update (readRecorded evals) i t j = P.cumulative j x - P.cumulative j a
      rw [Function.update_of_ne hji]
      exact evalBatch_values P oracle hpolicy a x hlegal.1 hx.1
        (hx.2.trans hlegal.2.2.1) (recordingObservers i) [(q, x)] j
        ((mem_recordingObservers i j).mpr hji)
  · exact Function.update_self i t (readRecorded evals)

end EnvyFreeResearch.Full.Chores
