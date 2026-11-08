import EnvyFreeResearch.Full.ChoresSubCorePhysicalLoop

/-! Exact execution of the stateful contested stage, including retained
stores on failure. No envy premise is needed for this finite operational
bound and record-reference invariant. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem stage_executes
    (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (processed : Finset Agent) (old : Node processed Parent (OrderedRecord n))
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card + 1 = Fintype.card Agent)
    (inherited : Allocation Agent Parent (OrderedRecord n)) (benchmark : Agent → Lex (ℝ × ℚ))
    (table : TrimTable (fun i (p : contestedParents processed old.assigned) => cachedValue agent i p.val)
      Set.univ (fun p => whole p.val)
      (stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark))
    (hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Store GlobalParent Payload →
      Node selected (contestedParents processed old.assigned) (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (Node selected (contestedParents processed old.assigned) (OrderedRecord n))))
    (oracle : AdaptiveOracle.Policy Query ℝ) (isCut : Query → Bool) (queryBound cutBound : ℕ → ℕ)
    (hcall : ∀ selected : Finset Agent, selected.card < Fintype.card (contestedParents processed old.assigned) →
      ∀ store, WellFormed view baseline store → ∀ before : Node selected (contestedParents processed old.assigned) (OrderedRecord n),
      Records view store (fun p => parent p.val) before.point →
      Records view store (fun p => parent p.val) (table.remainingCap selected) →
      ∀ prior : OracleProtocol.History Query ℝ,
      ∃ out trace, Executes oracle (recurse selected store before) prior out trace ∧
        WellFormed view baseline out.1 ∧ Extends store out.1 ∧
        (∀ returned, out.2 = some returned → Records view out.1 (fun p => parent p.val) returned.point) ∧
        trace.length ≤ queryBound selected.card ∧ trace.countP (fun qr => isCut qr.1) ≤ cutBound selected.card)
    (store : Store GlobalParent Payload) (hstore : WellFormed view baseline store)
    (hwhole : Records view store parent whole)
    (htable : TableRecords view agent (fun p : contestedParents processed old.assigned => parent p.val)
      (fun p : contestedParents processed old.assigned => whole p.val) _ store table)
    (prior : OracleProtocol.History Query ℝ) :
    ∃ out trace, Executes oracle (stageProgram agent whole processed old hcard hstage inherited benchmark table hOwner recurse store) prior out trace ∧
      WellFormed view baseline out.1 ∧ Extends store out.1 ∧
      (∀ allocation, out.2 = some allocation → Records view out.1 parent allocation.point) ∧
      trace.length ≤ ∑ j ∈ Finset.range processed.card, queryBound j ∧
      trace.countP (fun qr => isCut qr.1) ≤ ∑ j ∈ Finset.range processed.card, cutBound j := by
  classical
  let contested := contestedParents processed old.assigned
  let hne : ∀ p, (table.available p).Nonempty := fun p => ⟨contestedOwner processed old.assigned p, hOwner p⟩
  let initial := initialLoopState table hne (fun p => inheritedPreferred inherited.assigned p.val)
  have hInitial : Records view store (fun p : contested => parent p.val) initial.node.point :=
    initial_records view agent (fun p : contested => parent p.val) (fun p => whole p.val) _ store table htable
      (fun p => hwhole p.val) hne (fun p => inheritedPreferred inherited.assigned p.val)
  have hInitialCard : initial.selected.card ≤ Fintype.card contested := by
    change (Finset.univ.image (table.winner hne (fun p => inheritedPreferred inherited.assigned p.val))).card ≤ _
    exact Finset.card_image_le.trans_eq Finset.card_univ
  have hsize : initial.selected.card + (Fintype.card contested - initial.selected.card) = Fintype.card contested :=
    Nat.add_sub_of_le hInitialCard
  obtain ⟨loopOut, trace, hloop, hLoopStore, hLoopExt, hLoopRecords, hQ, hC⟩ := loop_executes view baseline agent
    (fun p : contested => parent p.val) (fun p => whole p.val) _ table (contestedOwner processed old.assigned) hOwner
    recurse oracle isCut queryBound cutBound hcall _ store hstore (fun p => hwhole p.val) htable initial hInitial hsize prior
  have hContestedCard : Fintype.card contested = processed.card := by simp only [contested, Fintype.card_coe, contestedParents_card]
  have hQ' : trace.length ≤ ∑ j ∈ Finset.range processed.card, queryBound j :=
    hQ.trans (loopBudget_le_full_sum queryBound _ _ _ (hsize.trans hContestedCard))
  have hC' : trace.countP (fun qr => isCut qr.1) ≤ ∑ j ∈ Finset.range processed.card, cutBound j :=
    hC.trans (loopBudget_le_full_sum cutBound _ _ _ (hsize.trans hContestedCard))
  let finish : Attempt GlobalParent Payload (LoopState Agent contested (OrderedRecord n)) →
      Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := fun returned =>
    match returned.2 with
    | none => .returned (returned.1, none)
    | some out => if hfull : out.selected.card = Fintype.card contested then
        .returned (returned.1, some (finishStage processed old.assigned hcard hstage (cachedValue agent) whole out hfull))
      else .returned (returned.1, none)
  cases hresult : loopOut.2 with
  | none =>
    have hreturn : Executes oracle (finish loopOut) (prior ++ trace) (loopOut.1, none) [] := by
      simp only [finish, hresult]
      exact Executes.returned _ _
    have hjoined := hloop.bind finish hreturn
    rw [List.append_nil] at hjoined
    refine ⟨(loopOut.1, none), trace, ?_, hLoopStore, hLoopExt, ?_, hQ', hC'⟩
    · convert hjoined using 1 <;> dsimp only [stageProgram, finish, initial, hne, contested] <;> congr 2
      funext returned
      cases returned.2 <;> dsimp only <;> split_ifs <;> rfl
    · intro allocation heq
      cases heq
  | some out =>
    obtain ⟨hfull, _, hrecords⟩ := hLoopRecords out hresult
    let allocation := finishStage processed old.assigned hcard hstage (cachedValue agent) whole out hfull
    have hreturn : Executes oracle (finish loopOut) (prior ++ trace) (loopOut.1, some allocation) [] := by
      simp only [finish, hresult, dite_eq_left hfull]
      exact Executes.returned _ _
    have hjoined := hloop.bind finish hreturn
    rw [List.append_nil] at hjoined
    refine ⟨(loopOut.1, some allocation), trace, ?_, hLoopStore, hLoopExt, ?_, hQ', hC'⟩
    · convert hjoined using 1 <;> dsimp only [stageProgram, finish, initial, hne, contested] <;> congr 2
      funext returned
      cases returned.2 <;> dsimp only <;> split_ifs <;> rfl
    · intro returned heq
      have heq' : allocation = returned := Option.some.inj heq
      subst returned
      exact finish_records view agent parent whole loopOut.1 processed old.assigned hcard hstage out hfull hrecords
        (Records.mono view hLoopExt parent whole hwhole)

end EnvyFreeResearch.Full.Chores.SubCorePhysical
