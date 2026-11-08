import EnvyFreeResearch.Full.ChoresUnionFullQuery

/-! A profile-independent stateful translation of virtual query programs.
The cost-dependent virtual oracle below is constructed only in the proof
of simulation; no valuation is an argument of the translated program. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ} {A : Type*}

def translate : Program (Query (Fin n)) ℝ A → List (Parent n) →
    Program (Query (Fin n)) ℝ (A × List (Parent n))
  | .returned a, cache => .returned (a,cache)
  | .failed, _ => .failed
  | .ask q k, cache => (fullQueryProgram cache q).bind (fun out =>
      match out.reply with
      | none => .failed
      | some r => translate (k r) out.cache)

structure SemanticState (P : Profile (Fin n)) (U : Set ℝ) where
  cache : List (Parent n)
  history : History (Query (Fin n)) ℝ
  valid : CacheValid P U cache

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
  (U : Set ℝ)

def StepSpec (S : SemanticState (measureProfile cost) U) (q : Query (Fin n))
    (step : OracleResult n × History (Query (Fin n)) ℝ) : Prop :=
  Executes oracle (fullQueryProgram S.cache q) S.history step.1 step.2 ∧
  step.2.length ≤ n*(2+cutCharge q) ∧
  step.2.countP (fun qr => isCutQuery qr.1) ≤ cutCharge q ∧
  ReplySpec (restrictedProfile cost U) q step.1.reply ∧
  CacheValid (measureProfile cost) U step.1.cache ∧
  (∀ x, Aligned S.cache x → Aligned step.1.cache x) ∧
  AcceptedBoundary q step.1 ∧
  (Geometry q → AlignedQuery step.1.cache q)

include hpolicy in
theorem exists_transition (S : SemanticState (measureProfile cost) U) (q : Query (Fin n)) :
    ∃ step, StepSpec cost oracle U S q step := by
  obtain ⟨out,trace,hexec,hlen,hcuts,hreply,hvalid,hold,hnew,hboundaries⟩ :=
    full_query_correct cost oracle hpolicy U S.cache S.valid q S.history
  exact ⟨(out,trace),hexec,hlen,hcuts,hreply,hvalid,hold,hnew,hboundaries⟩

def transition (S : SemanticState (measureProfile cost) U) (q : Query (Fin n)) :
    OracleResult n × History (Query (Fin n)) ℝ :=
  Classical.choose (exists_transition cost oracle hpolicy U S q)

theorem transition_spec (S : SemanticState (measureProfile cost) U) (q : Query (Fin n)) :
    StepSpec cost oracle U S q (transition cost oracle hpolicy U S q) :=
  Classical.choose_spec (exists_transition cost oracle hpolicy U S q)

def advanceState (S : SemanticState (measureProfile cost) U) (q : Query (Fin n)) :
    SemanticState (measureProfile cost) U where
  cache := (transition cost oracle hpolicy U S q).1.cache
  history := S.history ++ (transition cost oracle hpolicy U S q).2
  valid := (transition_spec cost oracle hpolicy U S q).2.2.2.2.1

/-- Reconstruct a legal virtual policy on every history, including histories
that will not occur. Actual simulation will prove agreement with replies;
the reconstruction itself need not trust supplied reply coordinates. -/
def historyState (initial : SemanticState (measureProfile cost) U)
    (history : History (Query (Fin n)) ℝ) : SemanticState (measureProfile cost) U :=
  history.foldl (fun S qr => advanceState cost oracle hpolicy U S qr.1) initial

theorem historyState_append_singleton (initial : SemanticState (measureProfile cost) U)
    (history : History (Query (Fin n)) ℝ) (q : Query (Fin n)) (r : ℝ) :
    historyState cost oracle hpolicy U initial (history++[(q,r)]) =
      advanceState cost oracle hpolicy U (historyState cost oracle hpolicy U initial history) q := by
  simp only [historyState,List.foldl_append,List.foldl_cons,List.foldl_nil]

def virtualPolicy (initial : SemanticState (measureProfile cost) U) :
    AdaptiveOracle.Policy (Query (Fin n)) ℝ := fun history q =>
  (transition cost oracle hpolicy U (historyState cost oracle hpolicy U initial history) q).1.reply

/-- This is an actual legal oracle for the restricted physical profile on
every history, not a presumed reply-simulation interface. -/
theorem virtual_policy_legal (initial : SemanticState (measureProfile cost) U) :
    AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U)
      (virtualPolicy cost oracle hpolicy U initial) := by
  intro history
  constructor
  · intro q r hr
    have hs := (transition_spec cost oracle hpolicy U
      (historyState cost oracle hpolicy U initial history) q).2.2.2.1
    change (transition cost oracle hpolicy U
      (historyState cost oracle hpolicy U initial history) q).1.reply = some r at hr
    refine ⟨?_,hs.2 r hr⟩
    by_contra hn
    have hnone := hs.1.mpr hn
    rw [hr] at hnone
    cases hnone
  · intro q hq
    have hs := (transition_spec cost oracle hpolicy U
      (historyState cost oracle hpolicy U initial history) q).2.2.2.1
    cases hr : (transition cost oracle hpolicy U
        (historyState cost oracle hpolicy U initial history) q).1.reply with
    | none => exact (hs.1.mp hr hq).elim
    | some r => exact ⟨r,hr⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
