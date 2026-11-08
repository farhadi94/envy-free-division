import EnvyFreeResearch.Full.ChoresUnionCoreParts

/-! Lifting active-agent queries to the original observer set preserves
the entire adaptive history and exact query counts. No child execution
budget is multiplied by this relabelling. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActiveCore
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n k : ℕ} {A : Type*}

def profile (P : Profile (Fin n)) (agent : Fin k → Fin n) : Profile (Fin k) where
  cumulative := fun i => P.cumulative (agent i)
  continuous := fun i => P.continuous (agent i)
  zero := fun i => P.zero (agent i)

def query (agent : Fin k → Fin n) : Query (Fin k) → Query (Fin n)
  | .eval i a b => .eval (agent i) a b
  | .cut i a b t => .cut (agent i) a b t

theorem legal_query (P : Profile (Fin n)) (agent : Fin k → Fin n) (q : Query (Fin k)) :
    Legal P (query agent q) ↔ Legal (profile P agent) q := by
  cases q <;> rfl

theorem valid_reply_query (P : Profile (Fin n)) (agent : Fin k → Fin n)
    (q : Query (Fin k)) (r : ℝ) :
    ValidReply P (query agent q) r ↔ ValidReply (profile P agent) q r := by
  cases q <;> rfl

def liftProgram (agent : Fin k → Fin n) : Program (Query (Fin k)) ℝ A → Program (Query (Fin n)) ℝ A
  | .returned a => .returned a
  | .failed => .failed
  | .ask q cont => .ask (query agent q) (fun r => liftProgram agent (cont r))

def liftHistory (agent : Fin k → Fin n) (history : History (Query (Fin k)) ℝ) :
    History (Query (Fin n)) ℝ := history.map (fun qr => (query agent qr.1, qr.2))

def localPolicy (agent : Fin k → Fin n) (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (prior : History (Query (Fin n)) ℝ) : AdaptiveOracle.Policy (Query (Fin k)) ℝ :=
  fun history q => oracle (prior ++ liftHistory agent history) (query agent q)

theorem local_policy_legal (P : Profile (Fin n)) (agent : Fin k → Fin n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (prior : History (Query (Fin n)) ℝ) :
    AdaptiveOracle.IsLegalPolicy (profile P agent) (localPolicy agent oracle prior) := by
  intro history
  constructor
  · intro q r hr
    obtain ⟨hlegal, hreply⟩ := (hpolicy (prior ++ liftHistory agent history)).sound (query agent q) r hr
    exact ⟨(legal_query P agent q).mp hlegal, (valid_reply_query P agent q r).mp hreply⟩
  · intro q hq
    exact (hpolicy (prior ++ liftHistory agent history)).complete (query agent q)
      ((legal_query P agent q).mpr hq)

theorem lift_executes (agent : Fin k → Fin n) (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (prior : History (Query (Fin n)) ℝ)
    {program : Program (Query (Fin k)) ℝ A} {history trace : History (Query (Fin k)) ℝ} {result : A}
    (hexec : Executes (localPolicy agent oracle prior) program history result trace) :
    Executes oracle (liftProgram agent program) (prior ++ liftHistory agent history) result
      (liftHistory agent trace) := by
  induction hexec with
  | returned a history => exact Executes.returned _ _
  | ask q cont history reply a tail hreply hnext ih =>
    apply Executes.ask (query agent q) (fun r => liftProgram agent (cont r))
      (prior ++ liftHistory agent history) reply a (liftHistory agent tail) hreply
    simpa only [liftHistory, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using ih

theorem lift_length (agent : Fin k → Fin n) (trace : History (Query (Fin k)) ℝ) :
    (liftHistory agent trace).length = trace.length := by simp only [liftHistory, List.length_map]

theorem lift_cuts (agent : Fin k → Fin n) (trace : History (Query (Fin k)) ℝ) :
    virtualCuts (liftHistory agent trace) = virtualCuts trace := by
  unfold virtualCuts liftHistory
  rw [List.countP_map]
  congr 1
  funext qr
  rcases qr with ⟨q, r⟩
  cases q <;> rfl

end EnvyFreeResearch.Full.Chores.ActiveCore
