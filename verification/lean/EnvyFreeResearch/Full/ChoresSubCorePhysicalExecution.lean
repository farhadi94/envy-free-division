import EnvyFreeResearch.Full.ChoresSubCorePhysicalStage

/-!
# Total bounded physical recursion before success replay

This theorem executes the actual cached-record program and retains its final
global store even on checked failure. Its only oracle premise is the exact
leaf recorder contract. No envy premise is used to obtain the finite table
or the complete physical query/Cut ledger. Success is a separate replay step.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

universe u v

variable {n : ℕ} {GlobalParent Payload Query : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]

theorem recursive_executes (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound : ℕ)
    (hEnsure : RecordsTargets view ensure baseline oracle isCut freshQueryBound) (fuel : ℕ) :
    ∀ (Agent : Type u) (Parent : Type v) [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent],
      ∀ (agent : Agent → Fin n) (parent : Parent → GlobalParent),
      0 < Fintype.card Agent → Fintype.card Agent ≤ fuel → Fintype.card Agent < Fintype.card Parent →
      ∀ (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
      (inherited : Allocation Agent Parent (OrderedRecord n)) (store : Store GlobalParent Payload),
      WellFormed view baseline store → Records view store parent whole →
      (∀ i, baseline (agent i) ≤ benchmark i) → ∀ prior : OracleProtocol.History Query ℝ,
      ∃ out trace, Executes oracle (recursiveProgram fuel Agent Parent view ensure agent parent whole benchmark inherited store) prior out trace ∧
        WellFormed view baseline out.1 ∧ Extends store out.1 ∧
        (∀ allocation, out.2 = some allocation → Records view out.1 parent allocation.point) ∧
        trace.length ≤ freshQueryBound * sourceBudget (Fintype.card Agent) ∧
        trace.countP (fun qr => isCut qr.1) ≤ sourceBudget (Fintype.card Agent) := by
  classical
  induction fuel with
  | zero =>
    intro Agent Parent _ _ _ _ agent parent hpositive hbound
    omega
  | succ fuel ih =>
    intro Agent Parent _ _ _ _ agent parent hpositive hbound hmany whole benchmark inherited store hstore hwhole hlower prior
    let newAgent : Agent := Classical.choice (Fintype.card_pos_iff.mp hpositive)
    let processed : Finset Agent := Finset.univ.erase newAgent
    have hstage : processed.card + 1 = Fintype.card Agent := by
      simpa only [processed, Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ newAgent)
    have hcard : processed.card < Fintype.card Parent := by omega
    let oldProgram : Program Query ℝ (Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n))) :=
      if hzero : processed.card = 0 then .returned (store, some (emptyRecordNode processed hzero whole)) else
        (recursiveProgram fuel processed Parent view ensure (fun i : processed => agent i.val) parent whole
          (fun i : processed => benchmark i.val)
          ⟨(⟨Subtype.val, Subtype.val_injective⟩ : processed ↪ Agent).trans inherited.assigned, inherited.point⟩ store).bind
          (fun out => .returned (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩)))
    have hOld : ∃ first firstTrace, Executes oracle oldProgram prior first firstTrace ∧
        WellFormed view baseline first.1 ∧ Extends store first.1 ∧
        (∀ node, first.2 = some node → Records view first.1 parent node.point) ∧
        firstTrace.length ≤ freshQueryBound * sourceBudget processed.card ∧
        firstTrace.countP (fun qr => isCut qr.1) ≤ sourceBudget processed.card := by
      by_cases hzero : processed.card = 0
      · refine ⟨(store, some (emptyRecordNode processed hzero whole)), [], ?_, hstore, Extends.refl store, ?_, Nat.zero_le _, Nat.zero_le _⟩
        · rw [show oldProgram = .returned (store, some (emptyRecordNode processed hzero whole)) by
            simp only [oldProgram, dite_eq_left hzero]]
          exact Executes.returned _ _
        · intro node heq
          have heq' : emptyRecordNode processed hzero whole = node := Option.some.inj heq
          subst node
          exact hwhole
      · obtain ⟨out, firstTrace, hexec, hout, hext, hrecords, hQ, hC⟩ := ih processed Parent
          (fun i : processed => agent i.val) parent (by simp only [Fintype.card_coe]; omega)
          (by simp only [Fintype.card_coe]; omega) (by simpa only [Fintype.card_coe] using hcard)
          whole (fun i : processed => benchmark i.val)
          ⟨(⟨Subtype.val, Subtype.val_injective⟩ : processed ↪ Agent).trans inherited.assigned, inherited.point⟩
          store hstore hwhole (fun i => hlower i.val) prior
        let result : Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n)) :=
          (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩))
        have hjoined := hexec.bind (fun out => Program.returned
          ((out.1, out.2.map (fun allocation => Node.mk allocation.assigned allocation.point)) :
            Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n))))
          (Executes.returned result (prior ++ firstTrace))
        rw [List.append_nil] at hjoined
        refine ⟨result, firstTrace, ?_, hout, hext, ?_, ?_, ?_⟩
        · dsimp only [oldProgram]
          rw [dite_eq_right hzero]
          exact hjoined
        · intro node heq
          cases ho : out.2 with
          | none =>
              simp only [result, ho, Option.map_none] at heq
              cases heq
          | some allocation =>
            have heq' : Node.mk allocation.assigned allocation.point = node := by
              simpa only [result, ho, Option.map_some, Option.some.injEq] using heq
            subst node
            exact hrecords allocation ho
        · simpa only [Fintype.card_coe] using hQ
        · simpa only [Fintype.card_coe] using hC
    obtain ⟨first, firstTrace, hOldExec, hFirstStore, hFirstExt, hFirstRecords, hFirstQ, hFirstC⟩ := hOld
    let stageCost := Fintype.card Agent * processed.card + ∑ j ∈ Finset.range processed.card, sourceBudget j
    have hBudget : sourceBudget processed.card + stageCost = sourceBudget (Fintype.card Agent) := by
      have h := sourceBudget_recurrence processed.card
      rw [hstage] at h
      simpa only [stageCost, Nat.add_assoc] using h.symm
    let afterOld : Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n)) →
        Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := fun previous =>
      match previous.2 with
      | none => .returned (previous.1, none)
      | some old => if hc : processed.card < Fintype.card Parent then
          let contested := contestedParents processed old.assigned
          let target := stageTarget processed old.assigned hc (fun i p => cachedValue agent i p (whole p)) benchmark
          (trimTableProgram view ensure agent (fun p : contested => parent p.val) (fun p => whole p.val) target previous.1).bind
            (fun prepared => match prepared.2 with
              | none => .returned (prepared.1, none)
              | some table => if ho : ∀ p, contestedOwner processed old.assigned p ∈ table.available p then
                  stageProgram agent whole processed old hc hstage inherited benchmark table ho
                    (fun selected current before => if hz : selected.card = 0 then
                      .returned (current, some (emptyRecordNode selected hz (table.remainingCap selected)))
                    else (recursiveProgram fuel selected contested view ensure (fun i : selected => agent i.val)
                      (fun p : contested => parent p.val) (table.remainingCap selected)
                      (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
                      ⟨before.assigned, before.point⟩ current).bind
                      (fun out => .returned (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩)))) prepared.1
                else .returned (prepared.1, none))
        else .returned (previous.1, none)
    have hAfter : ∃ out tail, Executes oracle (afterOld first) (prior ++ firstTrace) out tail ∧
        WellFormed view baseline out.1 ∧ Extends first.1 out.1 ∧
        (∀ allocation, out.2 = some allocation → Records view out.1 parent allocation.point) ∧
        tail.length ≤ freshQueryBound * stageCost ∧ tail.countP (fun qr => isCut qr.1) ≤ stageCost := by
      cases hfirst : first.2 with
      | none =>
        refine ⟨(first.1, none), [], ?_, hFirstStore, Extends.refl _, ?_, Nat.zero_le _, Nat.zero_le _⟩
        · simp only [afterOld, hfirst]
          exact Executes.returned _ _
        · intro allocation heq
          cases heq
      | some old =>
        let contested := contestedParents processed old.assigned
        let target := stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark
        have hContestedCard : Fintype.card contested = processed.card := by
          simp only [contested, Fintype.card_coe, contestedParents_card]
        have hWhole' : Records view first.1 parent whole := Records.mono view hFirstExt parent whole hwhole
        have hTargetLower : ∀ i, baseline (agent i) ≤ target i := fun i => (hlower i).trans
          (stageTarget_benchmark processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark i)
        by_cases hnonneg : ∀ i, 0 ≤ (ofLex (target i)).1
        · obtain ⟨prepared, table, middle, hTable, hPrepared, hPreparedExt, hTableRecords, hTableQ, hTableC⟩ :=
            trim_table_executes view ensure baseline oracle isCut freshQueryBound hEnsure agent
              (fun p : contested => parent p.val) (fun p => whole p.val) target first.1 hFirstStore
              (fun p => hWhole' p.val) hTargetLower hnonneg (prior ++ firstTrace)
          rw [hContestedCard] at hTableQ hTableC
          by_cases hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p
          · let recurse : ∀ selected : Finset Agent, Store GlobalParent Payload → Node selected contested (OrderedRecord n) →
                Program Query ℝ (Attempt GlobalParent Payload (Node selected contested (OrderedRecord n))) :=
              fun selected current before => if hz : selected.card = 0 then
                .returned (current, some (emptyRecordNode selected hz (table.remainingCap selected)))
              else (recursiveProgram fuel selected contested view ensure (fun i : selected => agent i.val)
                (fun p : contested => parent p.val) (table.remainingCap selected)
                (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
                ⟨before.assigned, before.point⟩ current).bind
                (fun out => .returned (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩)))
            have hcall : ∀ selected : Finset Agent, selected.card < Fintype.card contested →
                ∀ current, WellFormed view baseline current → ∀ before : Node selected contested (OrderedRecord n),
                Records view current (fun p => parent p.val) before.point →
                Records view current (fun p => parent p.val) (table.remainingCap selected) →
                ∀ previous : OracleProtocol.History Query ℝ,
                ∃ out trace, Executes oracle (recurse selected current before) previous out trace ∧
                  WellFormed view baseline out.1 ∧ Extends current out.1 ∧
                  (∀ returned, out.2 = some returned → Records view out.1 (fun p => parent p.val) returned.point) ∧
                  trace.length ≤ freshQueryBound * sourceBudget selected.card ∧
                  trace.countP (fun qr => isCut qr.1) ≤ sourceBudget selected.card := by
              intro selected hsmall current hcurrent before hbefore hcap previous
              by_cases hzero : selected.card = 0
              · refine ⟨(current, some (emptyRecordNode selected hzero (table.remainingCap selected))), [], ?_,
                  hcurrent, Extends.refl _, ?_, Nat.zero_le _, Nat.zero_le _⟩
                · simp only [recurse, dite_eq_left hzero]
                  exact Executes.returned _ _
                · intro returned heq
                  have heq' : emptyRecordNode selected hzero (table.remainingCap selected) = returned := Option.some.inj heq
                  subst returned
                  exact hcap
              · have hBenchmark : ∀ i : selected, baseline (agent i.val) ≤
                    ownValue selected before (fun i (p : contested) => cachedValue agent i p.val) i :=
                  fun i => record_baseline_le view baseline current hcurrent (parent (before.assigned i).val)
                    (before.point (before.assigned i)) (hbefore _) (agent i.val)
                obtain ⟨out, trace, hexec, hout, hext, hrecords, hQ, hC⟩ := ih selected contested
                  (fun i : selected => agent i.val) (fun p : contested => parent p.val)
                  (by simp only [Fintype.card_coe]; omega) (by simp only [Fintype.card_coe]; omega)
                  (by simpa only [Fintype.card_coe] using hsmall) (table.remainingCap selected)
                  (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
                  ⟨before.assigned, before.point⟩ current hcurrent hcap hBenchmark previous
                let result : Attempt GlobalParent Payload (Node selected contested (OrderedRecord n)) :=
                  (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩))
                have hjoined := hexec.bind (fun out => Program.returned
                  ((out.1, out.2.map (fun allocation => Node.mk allocation.assigned allocation.point)) :
                    Attempt GlobalParent Payload (Node selected contested (OrderedRecord n))))
                  (Executes.returned result (previous ++ trace))
                rw [List.append_nil] at hjoined
                refine ⟨result, trace, ?_, hout, hext, ?_, ?_, ?_⟩
                · dsimp only [recurse]
                  rw [dite_eq_right hzero]
                  exact hjoined
                · intro returned heq
                  cases ho : out.2 with
                  | none =>
                      simp only [result, ho, Option.map_none] at heq
                      cases heq
                  | some allocation =>
                    have heq' : Node.mk allocation.assigned allocation.point = returned := by
                      simpa only [result, ho, Option.map_some, Option.some.injEq] using heq
                    subst returned
                    exact hrecords allocation ho
                · simpa only [Fintype.card_coe] using hQ
                · simpa only [Fintype.card_coe] using hC
            obtain ⟨out, tail, hStage, hout, hext, hrecords, hStageQ, hStageC⟩ := stage_executes view baseline agent parent whole
              processed old hcard hstage inherited benchmark table hOwner recurse oracle isCut
              (fun k => freshQueryBound * sourceBudget k) sourceBudget hcall prepared hPrepared
              (Records.mono view hPreparedExt parent whole hWhole') hTableRecords ((prior ++ firstTrace) ++ middle)
            have hJoined : Executes oracle (afterOld first) (prior ++ firstTrace) out (middle ++ tail) := by
              simp only [afterOld, hfirst, dite_eq_left hcard]
              apply hTable.bind
              dsimp only
              rw [dite_eq_left hOwner]
              exact hStage
            refine ⟨out, middle ++ tail, hJoined, hout, hPreparedExt.trans hext, hrecords, ?_, ?_⟩
            · have hTailQ : tail.length ≤ freshQueryBound * ∑ j ∈ Finset.range processed.card, sourceBudget j := by
                simpa only [Finset.mul_sum] using hStageQ
              rw [List.length_append]
              exact (Nat.add_le_add hTableQ hTailQ).trans_eq (Nat.mul_add _ _ _).symm
            · rw [List.countP_append]
              exact Nat.add_le_add hTableC hStageC
          · have hJoined : Executes oracle (afterOld first) (prior ++ firstTrace) (prepared, none) middle := by
              simp only [afterOld, hfirst, dite_eq_left hcard]
              rw [← List.append_nil middle]
              apply hTable.bind
              dsimp only
              rw [dite_eq_right hOwner]
              exact Executes.returned _ _
            refine ⟨(prepared, none), middle, hJoined, hPrepared, hPreparedExt, ?_, ?_, ?_⟩
            · intro allocation heq
              cases heq
            · exact hTableQ.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
            · exact hTableC.trans (Nat.le_add_right _ _)
        · refine ⟨(first.1, none), [], ?_, hFirstStore, Extends.refl _, ?_, Nat.zero_le _, Nat.zero_le _⟩
          · simp only [afterOld, hfirst, dite_eq_left hcard]
            dsimp only [target] at hnonneg
            simp only [trimTableProgram, ite_eq_right hnonneg, Program.bind]
            exact Executes.returned _ _
          · intro allocation heq
            cases heq
    obtain ⟨out, tail, hAfterExec, hout, hext, hrecords, hTailQ, hTailC⟩ := hAfter
    have hJoined := hOldExec.bind afterOld hAfterExec
    refine ⟨out, firstTrace ++ tail, ?_, hout, hFirstExt.trans hext, hrecords, ?_, ?_⟩
    · rw [recursiveProgram, dite_eq_left hpositive]
      exact hJoined
    · rw [List.length_append]
      calc
        firstTrace.length + tail.length ≤ freshQueryBound * sourceBudget processed.card + freshQueryBound * stageCost :=
          Nat.add_le_add hFirstQ hTailQ
        _ = freshQueryBound * (sourceBudget processed.card + stageCost) := (Nat.mul_add _ _ _).symm
        _ = freshQueryBound * sourceBudget (Fintype.card Agent) := congrArg (freshQueryBound * ·) hBudget
    · rw [List.countP_append]
      exact (Nat.add_le_add hFirstC hTailC).trans_eq hBudget

end EnvyFreeResearch.Full.Chores.SubCorePhysical
