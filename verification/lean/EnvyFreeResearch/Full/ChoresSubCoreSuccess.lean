import EnvyFreeResearch.Full.ChoresSubCoreSuccessStage

/-! Closed physical population recursion. All smaller calls are discharged by
fuel induction, all target-primary guards are proved, and every returned
coordinate is an immutable physical record. The only leaf premise is exact
suffix recording, instantiated by the affine/clipped ordinary-query modules. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set QueryProgram Persistent SubCore
universe u v
variable {n : ℕ} {GlobalParent Payload Query : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]

theorem recursive_success (view : Payload → Record n)
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
      (∀ i, baseline (agent i) ≤ benchmark i) → Input view agent parent whole benchmark inherited store →
      ∀ prior : OracleProtocol.History Query ℝ,
      ∃ after out trace, Executes oracle (recursiveProgram fuel Agent Parent view ensure agent parent whole benchmark inherited store)
          prior (after,some out) trace ∧
        WellFormed view baseline after ∧ Extends store after ∧ Records view after parent out.point ∧
        SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out ∧
        (∀ i, 0 ≤ (ofLex (cachedValue agent i (out.assigned i) (out.point (out.assigned i)))).1) := by
  classical
  induction fuel with
  | zero =>
    intro Agent Parent _ _ _ _ agent parent hpositive hbound
    omega
  | succ fuel ih =>
    intro Agent Parent _ _ _ _ agent parent hpositive hbound hmany whole benchmark inherited store hstore hwhole hlower hinput prior
    let newAgent : Agent := Classical.choice (Fintype.card_pos_iff.mp hpositive)
    let processed : Finset Agent := Finset.univ.erase newAgent
    have hstage : processed.card+1 = Fintype.card Agent := by
      simpa only [processed,Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ newAgent)
    have hcard : processed.card < Fintype.card Parent := by omega
    let oldProgram : Program Query ℝ (Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n))) :=
      if hz : processed.card = 0 then .returned (store,some (emptyRecordNode processed hz whole)) else
        (recursiveProgram fuel processed Parent view ensure (fun i : processed => agent i.val) parent whole
          (fun i : processed => benchmark i.val)
          ⟨(⟨Subtype.val,Subtype.val_injective⟩ : processed ↪ Agent).trans inherited.assigned,inherited.point⟩ store).bind
          (fun out => .returned (out.1,out.2.map (fun allocation => ⟨allocation.assigned,allocation.point⟩)))
    have hOld : ∃ first old firstTrace, Executes oracle oldProgram prior (first,some old) firstTrace ∧
        WellFormed view baseline first ∧ Extends store first ∧ Records view first parent old.point ∧
        (∀ p, old.point p ≤ whole p) ∧
        (∀ i : processed, ∀ p, cachedValue agent i.val p (old.point p) ≤ ownValue processed old (cachedValue agent) i) ∧
        (∀ i : processed, benchmark i.val ≤ ownValue processed old (cachedValue agent) i) ∧
        (∀ p, (∀ i, old.assigned i ≠ p) → old.point p = whole p) := by
      by_cases hzero : processed.card = 0
      · have hnone : ∀ i : processed, False := by
          intro i
          have hp := Finset.card_pos.mpr ⟨i.val,i.property⟩
          omega
        refine ⟨store,emptyRecordNode processed hzero whole,[],?_,hstore,Extends.refl store,hwhole,
          fun _ => le_rfl,fun i _ => (hnone i).elim,fun i => (hnone i).elim,fun _ _ => rfl⟩
        simp only [oldProgram,dite_eq_left hzero]
        exact Executes.returned _ _
      · obtain ⟨first,out,firstTrace,hexec,hfirst,hext,hrecords,hcorrect,_⟩ := ih processed Parent
          (fun i : processed => agent i.val) parent (by simp only [Fintype.card_coe]; omega)
          (by simp only [Fintype.card_coe]; omega) (by simpa only [Fintype.card_coe] using hcard)
          whole (fun i : processed => benchmark i.val)
          ⟨(⟨Subtype.val,Subtype.val_injective⟩ : processed ↪ Agent).trans inherited.assigned,inherited.point⟩
          store hstore hwhole (fun i => hlower i.val) (hinput.restrict view agent parent whole benchmark inherited store processed) prior
        have hjoined := hexec.bind (fun result => Program.returned
          ((result.1,result.2.map (fun allocation => Node.mk allocation.assigned allocation.point)) :
            Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n))))
          (Executes.returned (first,some (Node.mk out.assigned out.point)) (prior++firstTrace))
        rw [List.append_nil] at hjoined
        refine ⟨first,⟨out.assigned,out.point⟩,firstTrace,?_,hfirst,hext,hrecords,fun p => (hcorrect.1 p).2,
          hcorrect.2.1,hcorrect.2.2.1,hcorrect.2.2.2.1⟩
        dsimp only [oldProgram]
        rw [dite_eq_right hzero]
        exact hjoined
    obtain ⟨first,old,firstTrace,hOldExec,hFirstStore,hFirstExt,hOldRecords,holdCap,hbest,hbench,hunused⟩ := hOld
    let contested := contestedParents processed old.assigned
    let target := stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark
    have hContestedCard : Fintype.card contested = processed.card := by simp only [contested,Fintype.card_coe,contestedParents_card]
    have hWhole' := Records.mono view hFirstExt parent whole hwhole
    have hInput' := Input.mono view agent parent whole benchmark inherited hFirstExt hinput
    have hTargetLower : ∀ i, baseline (agent i) ≤ target i := fun i => (hlower i).trans
      (stageTarget_benchmark processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark i)
    have hnonneg : ∀ i, 0 ≤ (ofLex (target i)).1 :=
      hinput.targets_nonnegative view agent parent whole benchmark inherited store processed old.assigned hcard
    obtain ⟨prepared,table,middle,hTable,hPrepared,hPreparedExt,hTableRecords,_,_⟩ :=
      trim_table_executes view ensure baseline oracle isCut freshQueryBound hEnsure agent
        (fun p : contested => parent p.val) (fun p => whole p.val) target first hFirstStore
        (fun p => hWhole' p.val) hTargetLower hnonneg (prior++firstTrace)
    have hWholePrepared := Records.mono view hPreparedExt parent whole hWhole'
    have hOldPrepared := Records.mono view hPreparedExt parent old.point hOldRecords
    let localTable := domainTable view agent (fun p : contested => parent p.val) (fun p => whole p.val) target prepared table hTableRecords
    have hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p :=
      Local.contested_owner_eligible (cachedValue agent) (domains view prepared parent) whole
        (fun i p => (strict_on_stored view prepared (parent p) (hPrepared.ordered _) (agent i)).monotoneOn)
        hWholePrepared processed old hcard benchmark hOldPrepared holdCap hbest hbench hunused localTable
    let recurse : ∀ selected : Finset Agent, Store GlobalParent Payload → Node selected contested (OrderedRecord n) →
        Program Query ℝ (Attempt GlobalParent Payload (Node selected contested (OrderedRecord n))) :=
      fun selected current before => if hz : selected.card = 0 then
        .returned (current,some (emptyRecordNode selected hz (table.remainingCap selected)))
      else (recursiveProgram fuel selected contested view ensure (fun i : selected => agent i.val)
        (fun p : contested => parent p.val) (table.remainingCap selected)
        (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
        ⟨before.assigned,before.point⟩ current).bind
        (fun out => .returned (out.1,out.2.map (fun allocation => ⟨allocation.assigned,allocation.point⟩)))
    have hcall : ∀ selected : Finset Agent, selected.card < Fintype.card contested →
        ∀ current, WellFormed view baseline current → ∀ before : Node selected contested (OrderedRecord n),
        Records view current (fun p => parent p.val) before.point →
        Records view current (fun p => parent p.val) (table.remainingCap selected) →
        SubCore.Inherited table ⟨selected,before⟩ → ∀ previous : OracleProtocol.History Query ℝ,
        ∃ after returned trace, Executes oracle (recurse selected current before) previous (after,some returned) trace ∧
          WellFormed view baseline after ∧ Extends current after ∧ Records view after (fun p => parent p.val) returned.point ∧
          SubCore.RecursiveCorrect table selected before returned := by
      intro selected hsmall current hcurrent before hbefore hcap hInherited previous
      by_cases hzero : selected.card = 0
      · have hnone : ∀ i : selected, False := by
          intro i
          have hp := Finset.card_pos.mpr ⟨i.val,i.property⟩
          omega
        refine ⟨current,emptyRecordNode selected hzero (table.remainingCap selected),[],?_,hcurrent,Extends.refl _,hcap,
          ⟨fun _ => ⟨mem_univ _,le_rfl⟩,fun i _ => (hnone i).elim,fun i => (hnone i).elim,fun _ _ => rfl⟩⟩
        simp only [recurse,dite_eq_left hzero]
        exact Executes.returned _ _
      · let subBenchmark := ownValue selected before (fun i (p : contested) => cachedValue agent i p.val)
        let subInherited : Allocation selected contested (OrderedRecord n) := ⟨before.assigned,before.point⟩
        have hsubInput : Input view (fun i : selected => agent i.val) (fun p : contested => parent p.val)
            (table.remainingCap selected) subBenchmark subInherited current := Or.inr
          ⟨⟨fun i => hInherited.1 (before.assigned i),fun _ => rfl,hInherited.2.2.1⟩,
            fun i => hbefore (before.assigned i),
            fun i => (hnonneg i.val).trans (primary_mono (hInherited.2.1 i))⟩
        have hBenchmark : ∀ i : selected, baseline (agent i.val) ≤ subBenchmark i := fun i =>
          record_baseline_le view baseline current hcurrent (parent (before.assigned i).val)
            (before.point (before.assigned i)) (hbefore _) (agent i.val)
        obtain ⟨after,out,trace,hexec,hafter,hext,hrecords,hcorrect,_⟩ := ih selected contested
          (fun i : selected => agent i.val) (fun p : contested => parent p.val)
          (by simp only [Fintype.card_coe]; omega) (by simp only [Fintype.card_coe]; omega)
          (by simpa only [Fintype.card_coe] using hsmall) (table.remainingCap selected) subBenchmark subInherited
          current hcurrent hcap hBenchmark hsubInput previous
        have hjoined := hexec.bind (fun result => Program.returned
          ((result.1,result.2.map (fun allocation => Node.mk allocation.assigned allocation.point)) :
            Attempt GlobalParent Payload (Node selected contested (OrderedRecord n))))
          (Executes.returned (after,some (Node.mk out.assigned out.point)) (previous++trace))
        rw [List.append_nil] at hjoined
        refine ⟨after,⟨out.assigned,out.point⟩,trace,?_,hafter,hext,hrecords,
          ⟨hcorrect.1,hcorrect.2.1,hcorrect.2.2.1,hcorrect.2.2.2.1⟩⟩
        dsimp only [recurse]
        rw [dite_eq_right hzero]
        exact hjoined
    obtain ⟨after,out,tail,hStage,hafter,hext,hrecords,hcorrect⟩ := stage_success view baseline agent parent whole
      processed old hcard hstage inherited benchmark holdCap hbest hbench hunused table hOwner recurse oracle hcall
      prepared hPrepared hWholePrepared hOldPrepared
      (Input.mono view agent parent whole benchmark inherited hPreparedExt hInput') hTableRecords ((prior++firstTrace)++middle)
    let afterOld : Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n)) →
        Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := fun previous =>
      match previous.2 with
      | none => .returned (previous.1,none)
      | some old => if hc : processed.card < Fintype.card Parent then
          let contested := contestedParents processed old.assigned
          let target := stageTarget processed old.assigned hc (fun i p => cachedValue agent i p (whole p)) benchmark
          (trimTableProgram view ensure agent (fun p : contested => parent p.val) (fun p => whole p.val) target previous.1).bind
            (fun prepared => match prepared.2 with
              | none => .returned (prepared.1,none)
              | some table => if ho : ∀ p, contestedOwner processed old.assigned p ∈ table.available p then
                  stageProgram agent whole processed old hc hstage inherited benchmark table ho
                    (fun selected current before => if hz : selected.card = 0 then
                      .returned (current,some (emptyRecordNode selected hz (table.remainingCap selected)))
                    else (recursiveProgram fuel selected contested view ensure (fun i : selected => agent i.val)
                      (fun p : contested => parent p.val) (table.remainingCap selected)
                      (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
                      ⟨before.assigned,before.point⟩ current).bind
                      (fun out => .returned (out.1,out.2.map (fun allocation => ⟨allocation.assigned,allocation.point⟩)))) prepared.1
                else .returned (prepared.1,none))
        else .returned (previous.1,none)
    have hAfter : Executes oracle (afterOld (first,some old)) (prior++firstTrace) (after,some out) (middle++tail) := by
      simp only [afterOld,dite_eq_left hcard]
      apply hTable.bind
      dsimp only
      rw [dite_eq_left hOwner]
      exact hStage
    have hJoined := hOldExec.bind afterOld hAfter
    refine ⟨after,out,firstTrace++(middle++tail),?_,hafter,hFirstExt.trans (hPreparedExt.trans hext),hrecords,hcorrect,
      Input.output_nonnegative view agent parent whole benchmark inherited out store hinput hmany hcorrect⟩
    rw [recursiveProgram,dite_eq_left hpositive]
    exact hJoined

end EnvyFreeResearch.Full.Chores.SubCorePhysical
