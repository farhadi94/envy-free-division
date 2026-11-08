import EnvyFreeResearch.Full.AdaptiveOracle

/-!
# Measurable encodings of actual oracle executions

Options use a disjoint union, lists use their length and padded coordinates,
and protocol constructors use finite disjoint unions. These are the usual
observable encodings, with no discrete sigma-algebra on real coordinates.
-/

namespace EnvyFreeResearch.Full.ProtocolMeasurable

open MeasureTheory OracleProtocol

universe u v w t

variable {α : Type u} {β : Type v} {γ : Type w} {X : Type t}

def optionCode : Option α → α ⊕ Unit
  | some a => Sum.inl a
  | none => Sum.inr ()

instance optionMeasurableSpace [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap optionCode inferInstance

theorem measurable_optionCode [MeasurableSpace α] :
    Measurable (optionCode (α := α)) := comap_measurable _

theorem measurable_some [MeasurableSpace α] : Measurable (some : α → Option α) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

theorem measurable_prod_sum_cases [MeasurableSpace X] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {left : X → α → γ} {right : X → β → γ}
    (hl : Measurable (fun p : X × α => left p.1 p.2))
    (hr : Measurable (fun p : X × β => right p.1 p.2)) :
    Measurable (fun p : X × (α ⊕ β) =>
      match p.2 with
      | .inl a => left p.1 a
      | .inr b => right p.1 b) := by
  convert (hl.sumElim hr).comp (MeasurableEquiv.prodSumDistrib X α β).measurable using 1
  funext p
  rcases p with ⟨x, s⟩
  cases s <;> rfl

theorem measurable_option_cases [MeasurableSpace X] [MeasurableSpace α]
    [MeasurableSpace β] {value : X → Option α} {present : X → α → β}
    {absent : X → β} (hv : Measurable value)
    (hp : Measurable (fun p : X × α => present p.1 p.2)) (ha : Measurable absent) :
    Measurable (fun x => match value x with
      | some a => present x a
      | none => absent x) := by
  have h := measurable_prod_sum_cases (right := fun x (_ : Unit) => absent x)
    hp (ha.comp measurable_fst)
  have hh := h.comp (measurable_id.prodMk (measurable_optionCode.comp hv))
  convert hh using 1
  funext x
  dsimp only [Function.comp_def, id_eq]
  cases value x <;> rfl

def listCode (xs : List α) : ℕ × (ℕ → Option α) := (xs.length, fun k => xs[k]?)

instance listMeasurableSpace [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.comap listCode inferInstance

theorem measurable_listCode [MeasurableSpace α] : Measurable (listCode (α := α)) :=
  comap_measurable _

theorem measurable_list_length [MeasurableSpace α] : Measurable (List.length (α := α)) :=
  measurable_fst.comp measurable_listCode

theorem measurable_list_getElem [MeasurableSpace α] (k : ℕ) :
    Measurable (fun xs : List α => xs[k]?) :=
  (measurable_pi_apply k).comp (measurable_snd.comp measurable_listCode)

theorem measurable_list_getElem_joint [MeasurableSpace α] :
    Measurable (fun p : List α × ℕ => p.1[p.2]?) :=
  measurable_from_prod_countable_left fun k => measurable_list_getElem k

theorem measurable_list_cons [MeasurableSpace α] :
    Measurable (fun p : α × List α => p.1 :: p.2) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun n : ℕ => n + 1)).comp
      (measurable_list_length.comp measurable_snd)
  · apply Measurable.of_eval
    intro k
    cases k with
    | zero => exact measurable_some.comp measurable_fst
    | succ k => exact (measurable_list_getElem k).comp measurable_snd

theorem measurable_list_singleton [MeasurableSpace α] :
    Measurable (fun x : α => [x]) :=
  measurable_list_cons.comp (measurable_id.prodMk measurable_const)

theorem measurable_list_append [MeasurableSpace α] :
    Measurable (fun p : List α × List α => p.1 ++ p.2) := by
  classical
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · simpa only [List.length_append, Function.comp_def] using
      ((measurable_of_countable (fun p : ℕ × ℕ => p.1 + p.2)).comp
      (((measurable_list_length (α := α)).comp (measurable_fst (β := List α))).prodMk
        ((measurable_list_length (α := α)).comp (measurable_snd (α := List α)))))
  · apply Measurable.of_eval
    intro k
    have hindex : Measurable (fun p : List α × List α => k - p.1.length) :=
      (measurable_of_countable (fun n : ℕ => k - n)).comp
        (measurable_list_length.comp measurable_fst)
    have htail := measurable_list_getElem_joint.comp (measurable_snd.prodMk hindex)
    have hhead : Measurable (fun p : List α × List α => p.1[k]?) :=
      (measurable_list_getElem k).comp measurable_fst
    have htest : MeasurableSet {p : List α × List α | k < p.1.length} :=
      measurableSet_lt measurable_const (measurable_list_length.comp measurable_fst)
    have hresult : Measurable (fun p : List α × List α =>
        if k < p.1.length then p.1[k]? else p.2[k - p.1.length]?) :=
      hhead.ite htest htail
    simpa only [listCode, Function.comp_def, List.getElem?_append] using hresult

def actionCode : Action α β → α ⊕ (β ⊕ Unit)
  | .ask q => .inl q
  | .returned o => .inr (.inl o)
  | .diverge => .inr (.inr ())

instance actionMeasurableSpace [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpace (Action α β) := MeasurableSpace.comap actionCode inferInstance

theorem measurable_actionCode [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (actionCode (α := α) (β := β)) := comap_measurable _

theorem measurable_action_ask [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Action.ask : α → Action α β) := by
  exact measurable_comap_iff.mpr measurable_inl

theorem measurable_action_returned [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Action.returned : β → Action α β) := by
  exact measurable_comap_iff.mpr (measurable_inr.comp measurable_inl)

theorem measurable_action_cases [MeasurableSpace X] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {value : X → Action α β} {ask : X → α → γ} {returned : X → β → γ}
    {diverge : X → γ} (hv : Measurable value)
    (ha : Measurable (fun p : X × α => ask p.1 p.2))
    (hr : Measurable (fun p : X × β => returned p.1 p.2)) (hd : Measurable diverge) :
    Measurable (fun x => match value x with
      | .ask q => ask x q
      | .returned o => returned x o
      | .diverge => diverge x) := by
  have hright : Measurable (fun p : X × (β ⊕ Unit) =>
      match p.2 with | .inl o => returned p.1 o | .inr _ => diverge p.1) := by
    convert measurable_prod_sum_cases (left := returned)
      (right := fun x (_ : Unit) => diverge x) hr (hd.comp measurable_fst) using 1
    funext p
    rcases p with ⟨x, s⟩
    cases s <;> rfl
  have h := measurable_prod_sum_cases (left := ask)
    (right := fun x (s : β ⊕ Unit) => match s with
    | .inl o => returned x o
    | .inr _ => diverge x) ha hright
  have hh := h.comp (measurable_id.prodMk (measurable_actionCode.comp hv))
  convert hh using 1
  funext x
  dsimp only [Function.comp_def, id_eq]
  cases value x <;> rfl

def stopCode : Stop α β → β ⊕ (Unit ⊕ (α ⊕ α))
  | .returned o => .inl o
  | .diverged => .inr (.inl ())
  | .illegal q => .inr (.inr (.inl q))
  | .exhausted q => .inr (.inr (.inr q))

instance stopMeasurableSpace [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpace (Stop α β) := MeasurableSpace.comap stopCode inferInstance

theorem measurable_stop_returned [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Stop.returned : β → Stop α β) := by
  exact measurable_comap_iff.mpr measurable_inl

theorem measurable_stop_illegal [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Stop.illegal : α → Stop α β) := by
  exact measurable_comap_iff.mpr (measurable_inr.comp (measurable_inr.comp measurable_inl))

theorem measurable_stop_exhausted [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Stop.exhausted : α → Stop α β) := by
  exact measurable_comap_iff.mpr (measurable_inr.comp (measurable_inr.comp measurable_inr))

def executionCode (e : Execution α β γ) : List (α × β) × Stop α γ :=
  (e.answered, e.stop)

instance executionMeasurableSpace [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : MeasurableSpace (Execution α β γ) :=
  MeasurableSpace.comap executionCode inferInstance

theorem measurable_executionCode [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : Measurable (executionCode (α := α) (β := β) (γ := γ)) :=
  comap_measurable _

theorem measurable_execution_answered [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : Measurable (Execution.answered (Query := α) (Reply := β)
      (Output := γ)) := measurable_fst.comp measurable_executionCode

theorem measurable_execution_stop [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : Measurable (Execution.stop (Query := α) (Reply := β)
      (Output := γ)) := measurable_snd.comp measurable_executionCode

theorem measurable_execution_mk [MeasurableSpace X] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {answered : X → List (α × β)} {stop : X → Stop α γ}
    (ha : Measurable answered) (hs : Measurable stop) :
    Measurable (fun x => (⟨answered x, stop x⟩ : Execution α β γ)) :=
  measurable_comap_iff.mpr (ha.prodMk hs)

theorem measurable_record_answer [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] :
    Measurable (fun p : (α × β) × Execution α β γ =>
      (⟨p.1 :: p.2.answered, p.2.stop⟩ : Execution α β γ)) :=
  measurable_execution_mk
    (measurable_list_cons.comp
      (measurable_fst.prodMk (measurable_execution_answered.comp measurable_snd)))
    (measurable_execution_stop.comp measurable_snd)

section Runs

variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}
variable [MeasurableSpace Tape] [MeasurableSpace Query] [MeasurableSpace Reply]
  [MeasurableSpace Output]

/-- Joint measurability of the actual bounded run, including the answered trace,
all four terminal outcomes, and arbitrary history-dependent replies. -/
theorem measurable_adaptive_run (next : Protocol Tape Query Reply Output)
    (oracle : AdaptiveOracle.Policy Query Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : History Query Reply × Query => oracle p.1 p.2))
    (fuel : ℕ) :
    Measurable (fun p : Tape × History Query Reply =>
      AdaptiveOracle.run next oracle p.1 fuel p.2) := by
  induction fuel with
  | zero =>
    have h := measurable_action_cases
      (ask := fun _ q => (⟨[], .exhausted q⟩ : Execution Query Reply Output))
      (returned := fun _ o => (⟨[], .returned o⟩ : Execution Query Reply Output))
      (diverge := fun _ => (⟨[], .diverged⟩ : Execution Query Reply Output)) hnext
      (measurable_execution_mk measurable_const
        (measurable_stop_exhausted.comp measurable_snd))
      (measurable_execution_mk measurable_const
        (measurable_stop_returned.comp measurable_snd))
      (measurable_const (a := (⟨[], .diverged⟩ : Execution Query Reply Output)))
    convert h using 1
    funext p
    rw [AdaptiveOracle.run]
    cases next p.1 p.2 <;> rfl
  | succ fuel ih =>
    have hreply : Measurable (fun p : (Tape × History Query Reply) × Query =>
        oracle p.1.2 p.2) :=
      horacle.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hqr : Measurable
        (fun p : ((Tape × History Query Reply) × Query) × Reply => (p.1.2, p.2)) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have htape : Measurable
        (fun p : ((Tape × History Query Reply) × Query) × Reply => p.1.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have hhistory : Measurable
        (fun p : ((Tape × History Query Reply) × Query) × Reply => p.1.1.2) :=
      measurable_snd.comp (measurable_fst.comp measurable_fst)
    have hupdated := measurable_list_append.comp
      (hhistory.prodMk (measurable_list_singleton.comp hqr))
    have htail := ih.comp (htape.prodMk hupdated)
    have hpresent := measurable_record_answer.comp (hqr.prodMk htail)
    have hask := measurable_option_cases
      (present := fun (p : (Tape × History Query Reply) × Query) reply =>
        let tail := AdaptiveOracle.run next oracle p.1.1 fuel (p.1.2 ++ [(p.2, reply)])
        (⟨(p.2, reply) :: tail.answered, tail.stop⟩ : Execution Query Reply Output))
      (absent := fun p => (⟨[], .illegal p.2⟩ : Execution Query Reply Output))
      hreply hpresent
      (measurable_execution_mk measurable_const
        (measurable_stop_illegal.comp measurable_snd))
    have h := measurable_action_cases
      (ask := fun p q => match oracle p.2 q with
        | some reply =>
          let tail := AdaptiveOracle.run next oracle p.1 fuel (p.2 ++ [(q, reply)])
          (⟨(q, reply) :: tail.answered, tail.stop⟩ : Execution Query Reply Output)
        | none => ⟨[], .illegal q⟩)
      (returned := fun _ o => (⟨[], .returned o⟩ : Execution Query Reply Output))
      (diverge := fun _ => (⟨[], .diverged⟩ : Execution Query Reply Output)) hnext hask
      (measurable_execution_mk measurable_const
        (measurable_stop_returned.comp measurable_snd))
      (measurable_const (a := (⟨[], .diverged⟩ : Execution Query Reply Output)))
    convert h using 1
    funext p
    rw [AdaptiveOracle.run]
    cases hn : next p.1 p.2 with
    | returned o => rfl
    | diverge => rfl
    | ask q => cases ho : oracle p.2 q <;> simp only [ho]

/-- Fixed-oracle measurability is derived through the proved embedding into
the history-dependent executor. -/
theorem measurable_run (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (fuel : ℕ) :
    Measurable (fun p : Tape × History Query Reply =>
      OracleProtocol.run next oracle p.1 fuel p.2) := by
  simpa only [AdaptiveOracle.fixed_policy_agrees] using
    measurable_adaptive_run next (fun _ => oracle) hnext
      (horacle.comp measurable_snd) fuel

theorem measurable_run_at_history (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable oracle) (fuel : ℕ) (history : History Query Reply) :
    Measurable (fun tape => OracleProtocol.run next oracle tape fuel history) :=
  (measurable_run next oracle hnext horacle fuel).comp
    (measurable_id.prodMk measurable_const)

/-- A common protocol against a jointly measurable family of input oracles.
The parameter is not revealed to `next`; it only determines oracle replies.
This covers random-input lower bounds without assuming the transcript map. -/
theorem measurable_run_parameterized {Parameter : Type*} [MeasurableSpace Parameter]
    (next : Protocol Tape Query Reply Output) (oracle : Parameter → Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : Parameter × Query => oracle p.1 p.2)) (fuel : ℕ) :
    Measurable (fun p : Parameter × Tape × History Query Reply =>
      OracleProtocol.run next (oracle p.1) p.2.1 fuel p.2.2) := by
  have hn : Measurable (fun p : Parameter × Tape × History Query Reply => next p.2.1 p.2.2) :=
    hnext.comp measurable_snd
  induction fuel with
  | zero =>
    have h := measurable_action_cases
      (ask := fun _ q => (⟨[], .exhausted q⟩ : Execution Query Reply Output))
      (returned := fun _ o => (⟨[], .returned o⟩ : Execution Query Reply Output))
      (diverge := fun _ => (⟨[], .diverged⟩ : Execution Query Reply Output)) hn
      (measurable_execution_mk measurable_const
        (measurable_stop_exhausted.comp measurable_snd))
      (measurable_execution_mk measurable_const
        (measurable_stop_returned.comp measurable_snd))
      measurable_const
    convert h using 1
    funext p
    rw [OracleProtocol.run]
    cases next p.2.1 p.2.2 <;> rfl
  | succ fuel ih =>
    have hreply : Measurable (fun p : (Parameter × Tape × History Query Reply) × Query =>
        oracle p.1.1 p.2) :=
      horacle.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hqr : Measurable (fun p :
        ((Parameter × Tape × History Query Reply) × Query) × Reply => (p.1.2, p.2)) := by
      fun_prop
    have hparameter : Measurable (fun p :
        ((Parameter × Tape × History Query Reply) × Query) × Reply => p.1.1.1) := by
      fun_prop
    have htape : Measurable (fun p :
        ((Parameter × Tape × History Query Reply) × Query) × Reply => p.1.1.2.1) := by
      fun_prop
    have hhistory : Measurable (fun p :
        ((Parameter × Tape × History Query Reply) × Query) × Reply => p.1.1.2.2) := by
      fun_prop
    have hupdated := measurable_list_append.comp
      (hhistory.prodMk (measurable_list_singleton.comp hqr))
    have htail := ih.comp (hparameter.prodMk (htape.prodMk hupdated))
    have hpresent := measurable_record_answer.comp (hqr.prodMk htail)
    have hask := measurable_option_cases
      (present := fun (p : (Parameter × Tape × History Query Reply) × Query) reply =>
        let tail := OracleProtocol.run next (oracle p.1.1) p.1.2.1 fuel
          (p.1.2.2 ++ [(p.2, reply)])
        (⟨(p.2, reply) :: tail.answered, tail.stop⟩ : Execution Query Reply Output))
      (absent := fun p => (⟨[], .illegal p.2⟩ : Execution Query Reply Output))
      hreply hpresent
      (measurable_execution_mk measurable_const
        (measurable_stop_illegal.comp measurable_snd))
    have h := measurable_action_cases
      (ask := fun p q => match oracle p.1 q with
        | some reply =>
          let tail := OracleProtocol.run next (oracle p.1) p.2.1 fuel (p.2.2 ++ [(q, reply)])
          (⟨(q, reply) :: tail.answered, tail.stop⟩ : Execution Query Reply Output)
        | none => ⟨[], .illegal q⟩)
      (returned := fun _ o => (⟨[], .returned o⟩ : Execution Query Reply Output))
      (diverge := fun _ => (⟨[], .diverged⟩ : Execution Query Reply Output)) hn hask
      (measurable_execution_mk measurable_const
        (measurable_stop_returned.comp measurable_snd)) measurable_const
    convert h using 1
    funext p
    rw [OracleProtocol.run]
    cases hnext' : next p.2.1 p.2.2 with
    | returned o => rfl
    | diverge => rfl
    | ask q => cases ho : oracle p.1 q <;> simp only [ho]

theorem measurable_run_parameterized_at_history {Parameter : Type*} [MeasurableSpace Parameter]
    (next : Protocol Tape Query Reply Output) (oracle : Parameter → Query → Option Reply)
    (hnext : Measurable (fun p : Tape × History Query Reply => next p.1 p.2))
    (horacle : Measurable (fun p : Parameter × Query => oracle p.1 p.2))
    (fuel : ℕ) (history : History Query Reply) :
    Measurable (fun p : Parameter × Tape =>
      OracleProtocol.run next (oracle p.1) p.2 fuel history) :=
  (measurable_run_parameterized next oracle hnext horacle fuel).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

end Runs

section IntervalQueries

variable {Agent : Type*}

def queryCode : IntervalOracle.Query Agent →
    (Agent × ℝ × ℝ) ⊕ (Agent × ℝ × ℝ × ℝ)
  | .eval i a b => .inl (i, a, b)
  | .cut i a b t => .inr (i, a, b, t)

instance queryMeasurableSpace [MeasurableSpace Agent] :
    MeasurableSpace (IntervalOracle.Query Agent) :=
  MeasurableSpace.comap queryCode inferInstance

theorem measurable_queryCode [MeasurableSpace Agent] :
    Measurable (queryCode (Agent := Agent)) := comap_measurable _

theorem measurable_query_eval [MeasurableSpace Agent] :
    Measurable (fun p : Agent × ℝ × ℝ => IntervalOracle.Query.eval p.1 p.2.1 p.2.2) :=
  measurable_comap_iff.mpr measurable_inl

theorem measurable_query_cut [MeasurableSpace Agent] :
    Measurable (fun p : Agent × ℝ × ℝ × ℝ =>
      IntervalOracle.Query.cut p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  measurable_comap_iff.mpr measurable_inr

theorem measurable_query_cases [MeasurableSpace Agent] [MeasurableSpace X]
    {f : IntervalOracle.Query Agent → X}
    (heval : Measurable (fun p : Agent × ℝ × ℝ => f (.eval p.1 p.2.1 p.2.2)))
    (hcut : Measurable (fun p : Agent × ℝ × ℝ × ℝ =>
      f (.cut p.1 p.2.1 p.2.2.1 p.2.2.2))) : Measurable f := by
  convert (heval.sumElim hcut).comp measurable_queryCode using 1
  funext q
  cases q <;> rfl

end IntervalQueries

end EnvyFreeResearch.Full.ProtocolMeasurable
