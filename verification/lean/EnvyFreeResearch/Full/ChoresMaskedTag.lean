import EnvyFreeResearch.Full.ChoresMaskedSimulation

/-! Embedding an ordinary physical suffix recorder into a parent-tagged
program preserves every reply, the complete preceding global history,
and its exact query and Cut counts. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Masked
open OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ} {Root A : Type*}

def tagProgram (p : Root) : Program (Query (Fin n)) ℝ A → Program (TaggedQuery Root n) ℝ A
  | .returned a => .returned a
  | .failed => .failed
  | .ask q k => .ask (p,q) (fun r => tagProgram p (k r))

def tagHistory (p : Root) (history : History (Query (Fin n)) ℝ) : History (TaggedQuery Root n) ℝ :=
  history.map (fun qr => ((p,qr.1),qr.2))

theorem tag_history_append (p : Root) (first second : History (Query (Fin n)) ℝ) :
    tagHistory p (first++second) = tagHistory p first++tagHistory p second := List.map_append

def localPolicy (oracle : AdaptiveOracle.Policy (TaggedQuery Root n) ℝ)
    (prior : History (TaggedQuery Root n) ℝ) (p : Root) : AdaptiveOracle.Policy (Query (Fin n)) ℝ :=
  fun history q => oracle (prior++tagHistory p history) (p,q)

theorem local_policy_legal (P : Root → Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (TaggedQuery Root n) ℝ) (hpolicy : IsLegalPolicy P oracle)
    (prior : History (TaggedQuery Root n) ℝ) (p : Root) :
    AdaptiveOracle.IsLegalPolicy (P p) (localPolicy oracle prior p) :=
  fun history => hpolicy (prior++tagHistory p history) p

theorem tag_executes (oracle : AdaptiveOracle.Policy (TaggedQuery Root n) ℝ)
    (prior : History (TaggedQuery Root n) ℝ) (p : Root)
    {program : Program (Query (Fin n)) ℝ A} {history trace : History (Query (Fin n)) ℝ} {result : A}
    (hexec : Executes (localPolicy oracle prior p) program history result trace) :
    Executes oracle (tagProgram p program) (prior++tagHistory p history) result (tagHistory p trace) := by
  induction hexec with
  | returned a history => exact Executes.returned _ _
  | ask q k history reply a tail hreply hnext ih =>
    apply Executes.ask (p,q) (fun r => tagProgram p (k r))
      (prior++tagHistory p history) reply a (tagHistory p tail) hreply
    simpa only [tagHistory,List.map_append,List.map_cons,List.map_nil,List.append_assoc] using ih

theorem tag_length (p : Root) (trace : History (Query (Fin n)) ℝ) :
    (tagHistory p trace).length = trace.length := by simp only [tagHistory,List.length_map]

theorem tag_cut_count (p : Root) (trace : History (Query (Fin n)) ℝ) :
    virtualCuts (tagHistory p trace) = trace.countP (fun qr => isCutQuery qr.1) := by
  simp only [virtualCuts,tagHistory,List.countP_map,Function.comp_def]

/-- An ordinary suffix-recording contract is usable at any parent of the
actual global history, with no extra virtual query or Cut factor. -/
theorem tag_correct (P : Root → Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (TaggedQuery Root n) ℝ) (hpolicy : IsLegalPolicy P oracle)
    (prior : History (TaggedQuery Root n) ℝ) (p : Root)
    (program : Program (Query (Fin n)) ℝ A) (good : A → Prop) (B C : ℕ)
    (hsource : ∀ policy, AdaptiveOracle.IsLegalPolicy (P p) policy →
      ∃ result trace, Executes policy program [] result trace ∧ good result ∧
        trace.length ≤ B ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ C) :
    ∃ result trace, Executes oracle (tagProgram p program) prior result trace ∧ good result ∧
      trace.length ≤ B ∧ virtualCuts trace ≤ C := by
  obtain ⟨result,trace,hexec,hgood,hlen,hcuts⟩ :=
    hsource (localPolicy oracle prior p) (local_policy_legal P oracle hpolicy prior p)
  refine ⟨result,tagHistory p trace,?_,hgood,?_,?_⟩
  · simpa only [tagHistory,List.map_nil,List.append_nil] using tag_executes oracle prior p hexec
  · simpa only [tag_length] using hlen
  · simpa only [tag_cut_count] using hcuts

end EnvyFreeResearch.Full.Chores.Masked
