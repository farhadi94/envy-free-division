import EnvyFreeResearch.Full.ChoresUnionTranslate

/-! Actual execution of the stateful program translation, with complete
physical query accounting. The virtual oracle is the concrete legal policy
constructed from the original physical query programs. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ} {A : Type*}

def virtualCuts (history : History (Query (Fin n)) ℝ) : ℕ :=
  history.countP (fun qr => isCutQuery qr.1)

theorem virtualCuts_cons (q : Query (Fin n)) (r : ℝ) (tail : History (Query (Fin n)) ℝ) :
    virtualCuts ((q,r)::tail) = cutCharge q+virtualCuts tail := by
  cases q <;> simp [virtualCuts,cutCharge,isCutQuery,Nat.add_comm]

theorem translate_executes (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (initial : SemanticState (measureProfile cost) U)
    {program : Program (Query (Fin n)) ℝ A} {history : History (Query (Fin n)) ℝ}
    {result : A} {virtualTrace : History (Query (Fin n)) ℝ}
    (hexec : Executes (virtualPolicy cost oracle hpolicy U initial) program history result virtualTrace) :
    ∃ physicalTrace : History (Query (Fin n)) ℝ,
      Executes oracle (translate program (historyState cost oracle hpolicy U initial history).cache)
        (historyState cost oracle hpolicy U initial history).history
        (result,(historyState cost oracle hpolicy U initial (history++virtualTrace)).cache) physicalTrace ∧
      physicalTrace.length ≤ n*(2*virtualTrace.length+virtualCuts virtualTrace) ∧
      virtualCuts physicalTrace ≤ virtualCuts virtualTrace := by
  induction hexec with
  | returned a history =>
    refine ⟨[],?_,by simp [virtualCuts],by simp [virtualCuts]⟩
    simpa only [translate,List.append_nil] using
      (Executes.returned (oracle := oracle)
        (a,(historyState cost oracle hpolicy U initial history).cache)
        (historyState cost oracle hpolicy U initial history).history)
  | ask q k history reply a tail hreply hnext ih =>
    let S := historyState cost oracle hpolicy U initial history
    let step := transition cost oracle hpolicy U S q
    have hstep : StepSpec cost oracle U S q step := transition_spec cost oracle hpolicy U S q
    have hr : step.1.reply = some reply := hreply
    obtain ⟨physicalTail,htail,hlen,hcuts⟩ := ih
    have hstate : historyState cost oracle hpolicy U initial (history++[(q,reply)]) =
        advanceState cost oracle hpolicy U S q :=
      historyState_append_singleton cost oracle hpolicy U initial history q reply
    have htail' : Executes oracle (translate (k reply) step.1.cache) (S.history++step.2)
        (a,(historyState cost oracle hpolicy U initial (history++((q,reply)::tail))).cache)
        physicalTail := by
      simpa only [hstate,advanceState,S,step,List.append_assoc,List.singleton_append] using htail
    refine ⟨step.2++physicalTail,?_,?_,?_⟩
    · rw [translate]
      change Executes oracle ((fullQueryProgram S.cache q).bind (fun out =>
        match out.reply with
        | none => Program.failed
        | some r => translate (k r) out.cache)) S.history _ _
      apply hstep.1.bind
      simpa only [hr] using htail'
    · rw [List.length_append]
      calc
        step.2.length+physicalTail.length ≤
            n*(2+cutCharge q)+n*(2*tail.length+virtualCuts tail) :=
          Nat.add_le_add hstep.2.1 hlen
        _ = n*(2*((q,reply)::tail).length+virtualCuts ((q,reply)::tail)) := by
          rw [List.length_cons,virtualCuts_cons]
          ring
    · change (step.2++physicalTail).countP (fun qr => isCutQuery qr.1) ≤ _
      rw [List.countP_append,virtualCuts_cons]
      exact Nat.add_le_add hstep.2.2.1 hcuts

end EnvyFreeResearch.Full.Chores.OrderedUnion
