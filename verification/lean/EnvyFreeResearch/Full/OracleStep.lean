import EnvyFreeResearch.Full.IntervalOracle

/-! One-step decomposition of actual adaptive oracle executions. -/
namespace EnvyFreeResearch.Full.OracleStep
open OracleProtocol IntervalOracle

variable {Tape Query Reply Output : Type*}

theorem zero_answers (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) :
    (run next oracle tape 0 history).answered = [] := by
  cases h : next tape history <;> simp [h]

theorem zero_not_illegal (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) (q : Query) :
    (run next oracle tape 0 history).stop ≠ .illegal q := by
  cases h : next tape history <;> simp [h]

/-- The query at an exhausted cap is exactly the next action on the full
answered history; no prospective query is guessed from another input. -/
theorem exhausted_next (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (q : Query)
    (h : (run next oracle tape fuel history).stop = .exhausted q) :
    next tape (history ++ (run next oracle tape fuel history).answered) = .ask q := by
  induction fuel generalizing history with
  | zero =>
    cases hn : next tape history with
    | returned out => simp [hn] at h
    | diverge => simp [hn] at h
    | ask r =>
      have hr : r = q := by simpa [hn] using h
      simp [hn, hr]
  | succ fuel ih =>
    cases hn : next tape history with
    | returned out => simp [hn] at h
    | diverge => simp [hn] at h
    | ask r =>
      cases ho : oracle r with
      | none => simp [hn, ho] at h
      | some ans =>
        have ht := ih (history ++ [(r, ans)]) (by simpa [hn, ho] using h)
        simpa [hn, ho, List.append_assoc] using ht

/-- Increasing the cap by one exposes at most one new answered request. -/
theorem succ_answer (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (q : Query) (r : Reply)
    (h : (q, r) ∈ (run next oracle tape (fuel + 1) history).answered) :
    (q, r) ∈ (run next oracle tape fuel history).answered ∨
      ((run next oracle tape fuel history).stop = .exhausted q ∧ oracle q = some r) := by
  rw [run_add_eq_resume] at h
  unfold resume at h
  cases hs : (run next oracle tape fuel history).stop with
  | returned out => exact Or.inl (by simpa [hs] using h)
  | diverged => exact Or.inl (by simpa [hs] using h)
  | illegal bad => exact Or.inl (by simpa [hs] using h)
  | exhausted nq =>
    have hn := exhausted_next next oracle tape fuel history nq hs
    cases ho : oracle nq with
    | none =>
      exact Or.inl (by simpa [hs, hn, ho] using h)
    | some nr =>
      simp only [hs] at h
      rw [run_succ_some _ _ _ 0 _ _ _ hn ho] at h
      simp only [zero_answers, List.mem_append, List.mem_singleton] at h
      rcases h with h | heq
      · exact Or.inl h
      · have hp := Prod.mk.inj heq
        rcases hp with ⟨rfl, rfl⟩
        exact Or.inr ⟨rfl, ho⟩

/-- A new terminal illegal call is the request exposed by the preceding cap. -/
theorem succ_illegal (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (q : Query)
    (h : (run next oracle tape (fuel + 1) history).stop = .illegal q) :
    (run next oracle tape fuel history).stop = .illegal q ∨
      ((run next oracle tape fuel history).stop = .exhausted q ∧ oracle q = none) := by
  rw [run_add_eq_resume] at h
  unfold resume at h
  cases hs : (run next oracle tape fuel history).stop with
  | returned out => simp [hs] at h
  | diverged => simp [hs] at h
  | illegal bad => exact Or.inl (by simpa [hs] using h)
  | exhausted nq =>
    have hn := exhausted_next next oracle tape fuel history nq hs
    cases ho : oracle nq with
    | none =>
      have hq : nq = q := by simpa [hs, hn, ho] using h
      subst nq
      exact Or.inr ⟨rfl, ho⟩
    | some nr =>
      simp only [hs] at h
      rw [run_succ_some _ _ _ 0 _ _ _ hn ho] at h
      exact False.elim (zero_not_illegal next oracle tape _ q h)

variable {Agent : Type*}

/-- Keeping the queried row exactly fixes the concrete least-root response. -/
theorem oracle_eq_of_row_eq (P P' : Profile Agent) (q : IntervalOracle.Query Agent)
    (hrow : P'.cumulative q.agent = P.cumulative q.agent) :
    IntervalOracle.oracle P' q = IntervalOracle.oracle P q := by
  classical
  have hlegal := legal_iff_of_endpoint_eq P P' q (congrFun hrow q.left) (congrFun hrow q.right)
  by_cases hold : Legal P q
  · have hnew : Legal P' q := hlegal.mpr hold
    cases q with
    | eval i a b =>
      change P'.cumulative i = P.cumulative i at hrow
      simp only [IntervalOracle.oracle, ite_eq_left hold, ite_eq_left hnew]
      rw [hrow]
    | cut i a b t =>
      change P'.cumulative i = P.cumulative i at hrow
      have hrnew := firstCut_spec P' i a b t hnew.2.1 hnew.2.2.2
      rw [hrow] at hrnew
      have heq := first_root_unique hrnew (firstCut_spec P i a b t hold.2.1 hold.2.2.2)
      simp only [IntervalOracle.oracle, ite_eq_left hold, ite_eq_left hnew, heq]
  · have hnew : ¬ Legal P' q := fun hp => hold (hlegal.mp hp)
    rw [(oracle_none_iff P' q).mpr hnew, (oracle_none_iff P q).mpr hold]

end EnvyFreeResearch.Full.OracleStep
