import EnvyFreeResearch.Full.ChoresComponentBoundary

/-! Endpoint provenance for the actual prefix recorder and persistent Core
store. These statements inspect successful executions; they need no
allocation-success or geometric provenance premise. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent
open scoped Classical

variable {n : ℕ}

theorem ofProtocol_map {Q R A B : Type*} (f : A → B)
    (next : Protocol Unit Q R A) (fuel : ℕ) (history : History Q R) :
    ofProtocol (mapProtocol f next) fuel history =
      (ofProtocol next fuel history).bind (fun out => .returned (f out)) := by
  induction fuel generalizing history with
  | zero =>
    conv_lhs => rw [ofProtocol]
    conv_rhs => rw [ofProtocol]
    cases h : next () history <;> simp only [mapProtocol, h, Program.bind]
  | succ fuel ih =>
    conv_lhs => rw [ofProtocol]
    conv_rhs => rw [ofProtocol]
    cases h : next () history <;> simp only [mapProtocol, h, Program.bind]
    congr 1
    funext r
    exact ih _

/-- After the initial physical Cut, all subsequent requests only record
values at its reply; a successful return keeps that exact point. -/
theorem endpoint_tail_point
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (c : Fin n) (a b t x : ℝ) (done : History (Query (Fin n)) ℝ)
    (fuel : ℕ) (prior : History (Query (Fin n)) ℝ)
    (out : EndpointRecord n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (endpointProtocol c a b t) fuel
      ((.cut c a b t, x) :: done)) prior out trace) : out.point = x := by
  induction fuel generalizing done prior trace with
  | zero =>
    cases hd : (recordingObservers c).drop done.length with
    | nil =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .returned (completedRecord c t x done) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
      rfl
    | cons j rest =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .ask (.eval j a x) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
  | succ fuel ih =>
    cases hd : (recordingObservers c).drop done.length with
    | nil =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .returned (completedRecord c t x done) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
      rfl
    | cons j rest =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .ask (.eval j a x) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h with
      | ask q next prior reply out tail hreply hnext =>
        apply ih (done ++ [(Query.eval j a x, reply)]) (prior ++ [(Query.eval j a x, reply)]) tail
        simpa only [List.cons_append] using hnext

/-- The physical endpoint recorder returns a point appearing as an actual
Cut reply in its own trace, for every successful execution and policy. -/
theorem endpoint_from_trace
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (c : Fin n) (a b t : ℝ) (prior : History (Query (Fin n)) ℝ)
    (out : EndpointRecord n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (endpointProgram c a b t) prior out trace) :
    out.point ∈ cutReplies trace := by
  cases n with
  | zero => exact Fin.elim0 c
  | succ n =>
    change Executes oracle (.ask (.cut c a b t) (fun reply =>
      ofProtocol (endpointProtocol c a b t) n [(.cut c a b t, reply)])) prior out trace at h
    cases h with
    | ask q next prior reply out tail hreply hnext =>
      have hp := endpoint_tail_point oracle c a b t reply [] n _ out tail hnext
      simp only [cutReplies, List.mem_cons]
      exact Or.inl hp

/-- Plateau branches reuse an immutable neighbor coordinate. The strict
branch's only new coordinate is an actual Cut reply. -/
theorem insertion_from_trace
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : Record n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (insertionProtocol left right i target) n []) prior out trace) :
    out.point = left.point ∨ out.point = right.point ∨ out.point ∈ cutReplies trace := by
  by_cases hl : target.1 = (left.formal i).1
  · simp only [insertionProtocol, ite_eq_left hl, ofProtocol] at h
    cases h
    exact Or.inl rfl
  · by_cases hr : target.1 = (right.formal i).1
    · simp only [insertionProtocol, ite_eq_right hl, ite_eq_left hr, ofProtocol] at h
      cases h
      exact Or.inr (Or.inl rfl)
    · simp only [insertionProtocol, ite_eq_right hl, ite_eq_right hr, ofProtocol_map] at h
      obtain ⟨e, first, second, he, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      exact Or.inr (Or.inr (endpoint_from_trace oracle i left.point right.point _ prior e first he))

/-- Every stored coordinate after lookup/insertion is either an input
coordinate or an actual Cut response; exact reuse performs no query. -/
theorem ensure_from_trace
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (records : List (Record n)) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : EnsureResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (ensureProtocol records i target) n []) prior out trace) :
    (∀ r ∈ out.records, (∃ old ∈ records, r.point = old.point) ∨ r.point ∈ cutReplies trace) ∧
    ((∃ old ∈ records, out.selected.point = old.point) ∨ out.selected.point ∈ cutReplies trace) := by
  have hlocvalid := locate_valid i target records
  cases hloc : locate i target records with
  | failed =>
    simp only [ensureProtocol, hloc, ofProtocol] at h
    cases h
  | reused r =>
    simp only [ensureProtocol, hloc, ofProtocol] at h
    cases h
    rw [hloc] at hlocvalid
    exact ⟨fun s hs => Or.inl ⟨s, hs, rfl⟩, Or.inl ⟨r, hlocvalid.1, rfl⟩⟩
  | bracket pre left right post =>
    rw [hloc] at hlocvalid
    have hdecomp : records = pre ++ left :: right :: post := hlocvalid.1
    simp only [ensureProtocol, hloc, ofProtocol_map] at h
    obtain ⟨fresh, first, second, hfresh, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    have hf := insertion_from_trace oracle left right i target prior fresh first hfresh
    have hleft : left ∈ records := by simp [hdecomp]
    have hright : right ∈ records := by simp [hdecomp]
    have hnew : (∃ old ∈ records, fresh.point = old.point) ∨ fresh.point ∈ cutReplies first := by
      rcases hf with hleft' | hright' | hcut
      · exact Or.inl ⟨left, hleft, hleft'⟩
      · exact Or.inl ⟨right, hright, hright'⟩
      · exact Or.inr hcut
    refine ⟨?_, hnew⟩
    intro r hr
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hr | rfl | rfl | rfl | hr
    · exact Or.inl ⟨r, by simp [hdecomp, hr], rfl⟩
    · exact Or.inl ⟨_, hleft, rfl⟩
    · exact hnew
    · exact Or.inl ⟨_, hright, rfl⟩
    · exact Or.inl ⟨r, by simp [hdecomp, hr], rfl⟩

/-- The actual shared store changes only the selected parent's list, and all
new coordinates obey the same provenance rule. -/
theorem global_from_trace
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (store : Store n) (i p : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : StoreResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ensureGlobalProgram store i p target) prior out trace) :
    (∀ q r, r ∈ out.store q → (∃ old ∈ store q, r.point = old.point) ∨ r.point ∈ cutReplies trace) ∧
    ((∃ old ∈ store p, out.selected.point = old.point) ∨ out.selected.point ∈ cutReplies trace) := by
  obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hsecond
  simp only [List.append_nil] at htrace
  subst trace
  obtain ⟨hrecords, hselected⟩ := ensure_from_trace oracle (store p) i target prior result first hfirst
  refine ⟨?_, hselected⟩
  intro q r hr
  by_cases hq : q = p
  · subst q
    simp only [Function.update_self] at hr
    exact hrecords r hr
  · simp only [Function.update_of_ne hq] at hr
    exact Or.inl ⟨r, hr, rfl⟩

end EnvyFreeResearch.Full.Chores.Boundary
