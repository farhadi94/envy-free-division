import EnvyFreeResearch.Full.ChoresSubCoreSuccess

/-! The successful physical recursive execution and its complete ledger
refer to the same trace, by determinism of the full-history oracle policy. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set QueryProgram Persistent SubCore
variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem recursive_correct (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound fuel : ℕ)
    (hEnsure : RecordsTargets view ensure baseline oracle isCut freshQueryBound)
    (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (hpositive : 0 < Fintype.card Agent) (hbound : Fintype.card Agent ≤ fuel)
    (hmany : Fintype.card Agent < Fintype.card Parent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (inherited : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload)
    (hstore : WellFormed view baseline store) (hwhole : Records view store parent whole)
    (hlower : ∀ i, baseline (agent i) ≤ benchmark i)
    (hinput : Input view agent parent whole benchmark inherited store)
    (prior : OracleProtocol.History Query ℝ) :
    ∃ after out trace, Executes oracle (recursiveProgram fuel Agent Parent view ensure agent parent whole benchmark inherited store)
        prior (after,some out) trace ∧
      WellFormed view baseline after ∧ Extends store after ∧ Records view after parent out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out ∧
      (∀ i, 0 ≤ (ofLex (cachedValue agent i (out.assigned i) (out.point (out.assigned i)))).1) ∧
      trace.length ≤ freshQueryBound * sourceBudget (Fintype.card Agent) ∧
      trace.countP (fun qr => isCut qr.1) ≤ sourceBudget (Fintype.card Agent) := by
  obtain ⟨after,out,trace,hexec,hafter,hext,hrecords,hcorrect,hnonneg⟩ :=
    recursive_success view ensure baseline oracle isCut freshQueryBound hEnsure fuel Agent Parent agent parent
      hpositive hbound hmany whole benchmark inherited store hstore hwhole hlower hinput prior
  obtain ⟨attempt,ledgerTrace,hledger,_,_,_,hQ,hC⟩ :=
    recursive_executes view ensure baseline oracle isCut freshQueryBound hEnsure fuel Agent Parent agent parent
      hpositive hbound hmany whole benchmark inherited store hstore hwhole hlower prior
  have ht : ledgerTrace = trace := (hledger.deterministic hexec).2
  exact ⟨after,out,trace,hexec,hafter,hext,hrecords,hcorrect,hnonneg,ht ▸ hQ,ht ▸ hC⟩

def entryAllocation (hcard : Fintype.card Agent ≤ Fintype.card Parent) (point : Parent → OrderedRecord n) :
    Allocation Agent Parent (OrderedRecord n) :=
  ⟨(Fintype.equivFin Agent).toEmbedding.trans
    ((Fin.castLEEmb hcard).trans (Fintype.equivFin Parent).symm.toEmbedding),point⟩

end EnvyFreeResearch.Full.Chores.SubCorePhysical
