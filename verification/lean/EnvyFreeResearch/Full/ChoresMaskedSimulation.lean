import EnvyFreeResearch.Full.ChoresMaskedQuery

/-! Stateful compilation of parent-tagged, observer-masked query programs
into the original Eval/Cut oracle. The program does not receive the cost
measures. A virtual policy is constructed in the proof from actual finite
physical executions, including the complete preceding physical history. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Masked
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n : ℕ} {Root A : Type*}

def IsLegalPolicy (P : Root → Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (TaggedQuery Root n) ℝ) : Prop :=
  ∀ history p, IsLegalOracle (P p) (fun q => oracle history (p,q))

def translate : Program (TaggedQuery Root n) ℝ A → Cache Root n →
    Program (Query (Fin n)) ℝ (A × Cache Root n)
  | .returned a, cache => .returned (a,cache)
  | .failed, _ => .failed
  | .ask q k, cache => (dispatchProgram cache q).bind (fun out =>
      match out.reply with
      | none => .failed
      | some r => translate (k r) out.cache)

structure SemanticState (P : Profile (Fin n)) (domains : Root → Fin n → Set ℝ) where
  cache : Cache Root n
  history : History (Query (Fin n)) ℝ
  valid : CacheCorrect P domains cache

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
  (domains : Root → Fin n → Set ℝ)

def StepSpec (S : SemanticState (measureProfile cost) domains) (q : TaggedQuery Root n)
    (step : Result Root n × History (Query (Fin n)) ℝ) : Prop :=
  Executes oracle (dispatchProgram S.cache q) S.history step.1 step.2 ∧
  step.2.length ≤ n*(2+cutCharge q.2) ∧
  step.2.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q.2 ∧
  ReplySpec (rowProfile cost (domains q.1)) q.2 step.1.reply ∧
  CacheCorrect (measureProfile cost) domains step.1.cache

include hpolicy in
theorem exists_transition (S : SemanticState (measureProfile cost) domains) (q : TaggedQuery Root n) :
    ∃ step, StepSpec cost oracle domains S q step := by
  obtain ⟨out,trace,hexec,hlen,hcuts,hreply,hvalid⟩ :=
    dispatch_correct cost oracle hpolicy domains S.cache S.valid q S.history
  exact ⟨(out,trace),hexec,hlen,hcuts,hreply,hvalid⟩

def transition (S : SemanticState (measureProfile cost) domains) (q : TaggedQuery Root n) :
    Result Root n × History (Query (Fin n)) ℝ :=
  Classical.choose (exists_transition cost oracle hpolicy domains S q)

theorem transition_spec (S : SemanticState (measureProfile cost) domains) (q : TaggedQuery Root n) :
    StepSpec cost oracle domains S q (transition cost oracle hpolicy domains S q) :=
  Classical.choose_spec (exists_transition cost oracle hpolicy domains S q)

def advanceState (S : SemanticState (measureProfile cost) domains) (q : TaggedQuery Root n) :
    SemanticState (measureProfile cost) domains where
  cache := (transition cost oracle hpolicy domains S q).1.cache
  history := S.history ++ (transition cost oracle hpolicy domains S q).2
  valid := (transition_spec cost oracle hpolicy domains S q).2.2.2.2

def historyState (initial : SemanticState (measureProfile cost) domains)
    (history : History (TaggedQuery Root n) ℝ) : SemanticState (measureProfile cost) domains :=
  history.foldl (fun S qr => advanceState cost oracle hpolicy domains S qr.1) initial

theorem historyState_append_singleton (initial : SemanticState (measureProfile cost) domains)
    (history : History (TaggedQuery Root n) ℝ) (q : TaggedQuery Root n) (r : ℝ) :
    historyState cost oracle hpolicy domains initial (history++[(q,r)]) =
      advanceState cost oracle hpolicy domains (historyState cost oracle hpolicy domains initial history) q := by
  simp only [historyState,List.foldl_append,List.foldl_cons,List.foldl_nil]

def virtualPolicy (initial : SemanticState (measureProfile cost) domains) :
    AdaptiveOracle.Policy (TaggedQuery Root n) ℝ := fun history q =>
  (transition cost oracle hpolicy domains
    (historyState cost oracle hpolicy domains initial history) q).1.reply

theorem virtual_policy_legal (initial : SemanticState (measureProfile cost) domains) :
    IsLegalPolicy (fun p => rowProfile cost (domains p))
      (virtualPolicy cost oracle hpolicy domains initial) := by
  intro history p
  constructor
  · intro q r hr
    have hs := (transition_spec cost oracle hpolicy domains
      (historyState cost oracle hpolicy domains initial history) (p,q)).2.2.2.1
    change (transition cost oracle hpolicy domains
      (historyState cost oracle hpolicy domains initial history) (p,q)).1.reply = some r at hr
    refine ⟨?_,hs.2 r hr⟩
    by_contra hn
    have hnone := hs.1.mpr hn
    rw [hr] at hnone
    cases hnone
  · intro q hq
    have hs := (transition_spec cost oracle hpolicy domains
      (historyState cost oracle hpolicy domains initial history) (p,q)).2.2.2.1
    cases hr : (transition cost oracle hpolicy domains
        (historyState cost oracle hpolicy domains initial history) (p,q)).1.reply with
    | none => exact (hs.1.mp hr hq).elim
    | some r => exact ⟨r,hr⟩

def virtualCuts (history : History (TaggedQuery Root n) ℝ) : ℕ :=
  history.countP (fun qr => isCutQuery qr.1.2)

theorem virtualCuts_cons (q : TaggedQuery Root n) (r : ℝ) (tail : History (TaggedQuery Root n) ℝ) :
    virtualCuts ((q,r)::tail) = cutCharge q.2+virtualCuts tail := by
  rcases q with ⟨p,q⟩
  cases q <;> simp [virtualCuts,cutCharge,isCutQuery,Nat.add_comm]

theorem translate_executes (initial : SemanticState (measureProfile cost) domains)
    {program : Program (TaggedQuery Root n) ℝ A} {history : History (TaggedQuery Root n) ℝ}
    {result : A} {virtualTrace : History (TaggedQuery Root n) ℝ}
    (hexec : Executes (virtualPolicy cost oracle hpolicy domains initial) program history result virtualTrace) :
    ∃ physicalTrace : History (Query (Fin n)) ℝ,
      Executes oracle (translate program (historyState cost oracle hpolicy domains initial history).cache)
        (historyState cost oracle hpolicy domains initial history).history
        (result,(historyState cost oracle hpolicy domains initial (history++virtualTrace)).cache) physicalTrace ∧
      physicalTrace.length ≤ n*(2*virtualTrace.length+virtualCuts virtualTrace) ∧
      physicalTrace.countP (fun qr => isCutQuery qr.1) ≤ virtualCuts virtualTrace := by
  induction hexec with
  | returned a history =>
    refine ⟨[],?_,by simp [virtualCuts],by simp [virtualCuts]⟩
    simpa only [translate,List.append_nil] using
      (Executes.returned (oracle := oracle)
        (a,(historyState cost oracle hpolicy domains initial history).cache)
        (historyState cost oracle hpolicy domains initial history).history)
  | ask q k history reply a tail hreply hnext ih =>
    let S := historyState cost oracle hpolicy domains initial history
    let step := transition cost oracle hpolicy domains S q
    have hstep : StepSpec cost oracle domains S q step := transition_spec cost oracle hpolicy domains S q
    have hr : step.1.reply = some reply := hreply
    obtain ⟨physicalTail,htail,hlen,hcuts⟩ := ih
    have hstate : historyState cost oracle hpolicy domains initial (history++[(q,reply)]) =
        advanceState cost oracle hpolicy domains S q :=
      historyState_append_singleton cost oracle hpolicy domains initial history q reply
    have htail' : Executes oracle (translate (k reply) step.1.cache) (S.history++step.2)
        (a,(historyState cost oracle hpolicy domains initial (history++((q,reply)::tail))).cache)
        physicalTail := by
      simpa only [hstate,advanceState,S,step,List.append_assoc,List.singleton_append] using htail
    refine ⟨step.2++physicalTail,?_,?_,?_⟩
    · rw [translate]
      change Executes oracle ((dispatchProgram S.cache q).bind (fun out =>
        match out.reply with
        | none => Program.failed
        | some r => translate (k r) out.cache)) S.history _ _
      apply hstep.1.bind
      simpa only [hr] using htail'
    · rw [List.length_append]
      calc
        step.2.length+physicalTail.length ≤
            n*(2+cutCharge q.2)+n*(2*tail.length+virtualCuts tail) :=
          Nat.add_le_add hstep.2.1 hlen
        _ = n*(2*((q,reply)::tail).length+virtualCuts ((q,reply)::tail)) := by
          rw [List.length_cons,virtualCuts_cons]
          ring
    · rw [List.countP_append,virtualCuts_cons]
      exact Nat.add_le_add hstep.2.2.1 hcuts

include hpolicy in
/-- Compile once, outside all population recursions. The physical ledger
has one polynomial routing overhead, rather than one factor per recursion. -/
theorem compile_correct (program : Program (TaggedQuery Root n) ℝ A)
    (cache : Cache Root n) (hc : CacheCorrect (measureProfile cost) domains cache)
    (prior : History (Query (Fin n)) ℝ) (good : A → Prop) (B C : ℕ)
    (hsource : ∀ virtual, IsLegalPolicy (fun p => rowProfile cost (domains p)) virtual →
      ∃ result trace, Executes virtual program [] result trace ∧ good result ∧
        trace.length ≤ B ∧ virtualCuts trace ≤ C) :
    ∃ result next trace,
      Executes oracle (translate program cache) prior (result,next) trace ∧ good result ∧
      trace.length ≤ n*(2*B+C) ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ C ∧
      CacheCorrect (measureProfile cost) domains next := by
  let initial : SemanticState (measureProfile cost) domains := ⟨cache,prior,hc⟩
  obtain ⟨result,sourceTrace,hexec,hgood,hlen,hcuts⟩ :=
    hsource (virtualPolicy cost oracle hpolicy domains initial)
      (virtual_policy_legal cost oracle hpolicy domains initial)
  obtain ⟨trace,hrun,hql,hcl⟩ := translate_executes cost oracle hpolicy domains initial hexec
  refine ⟨result,(historyState cost oracle hpolicy domains initial sourceTrace).cache,trace,
    ?_,hgood,?_,hcl.trans hcuts,(historyState cost oracle hpolicy domains initial sourceTrace).valid⟩
  · simpa only [historyState,List.foldl_nil,List.nil_append,initial] using hrun
  · exact hql.trans (Nat.mul_le_mul_left n
      (Nat.add_le_add (Nat.mul_le_mul_left 2 hlen) hcuts))

end EnvyFreeResearch.Full.Chores.Masked
