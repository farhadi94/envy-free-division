import EnvyFreeResearch.Full.ChoresSubCoreSuccessLoop

/-! Successful execution of the actual physical contested stage. Both the
owner tie rule and final whole-parent assignment are derived on retained rows. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set QueryProgram Persistent SubCore
variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem stage_success
    (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (processed : Finset Agent) (old : Node processed Parent (OrderedRecord n))
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card+1 = Fintype.card Agent)
    (inherited : Allocation Agent Parent (OrderedRecord n)) (benchmark : Agent → Lex (ℝ × ℚ))
    (holdCap : ∀ p, old.point p ≤ whole p)
    (hbest : ∀ i : processed, ∀ p, cachedValue agent i.val p (old.point p) ≤ ownValue processed old (cachedValue agent) i)
    (hbench : ∀ i : processed, benchmark i.val ≤ ownValue processed old (cachedValue agent) i)
    (hunused : ∀ p, (∀ i, old.assigned i ≠ p) → old.point p = whole p)
    (table : TrimTable (fun i (p : contestedParents processed old.assigned) => cachedValue agent i p.val)
      univ (fun p => whole p.val)
      (stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark))
    (hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Store GlobalParent Payload →
      Node selected (contestedParents processed old.assigned) (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (Node selected (contestedParents processed old.assigned) (OrderedRecord n))))
    (oracle : AdaptiveOracle.Policy Query ℝ)
    (hcall : ∀ selected : Finset Agent, selected.card < Fintype.card (contestedParents processed old.assigned) →
      ∀ store, WellFormed view baseline store → ∀ before : Node selected (contestedParents processed old.assigned) (OrderedRecord n),
      Records view store (fun p => parent p.val) before.point →
      Records view store (fun p => parent p.val) (table.remainingCap selected) →
      SubCore.Inherited table ⟨selected,before⟩ → ∀ prior : OracleProtocol.History Query ℝ,
      ∃ after returned trace, Executes oracle (recurse selected store before) prior (after,some returned) trace ∧
        WellFormed view baseline after ∧ Extends store after ∧ Records view after (fun p => parent p.val) returned.point ∧
        SubCore.RecursiveCorrect table selected before returned)
    (store : Store GlobalParent Payload) (hstore : WellFormed view baseline store)
    (hwhole : Records view store parent whole) (hold : Records view store parent old.point)
    (hinput : Input view agent parent whole benchmark inherited store)
    (htable : TableRecords view agent (fun p : contestedParents processed old.assigned => parent p.val)
      (fun p : contestedParents processed old.assigned => whole p.val) _ store table)
    (prior : OracleProtocol.History Query ℝ) :
    ∃ after out trace, Executes oracle (stageProgram agent whole processed old hcard hstage inherited benchmark table hOwner recurse store)
        prior (after,some out) trace ∧
      WellFormed view baseline after ∧ Extends store after ∧ Records view after parent out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out := by
  classical
  let contested := contestedParents processed old.assigned
  let target := stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark
  let hne : ∀ p, (table.available p).Nonempty := fun p => ⟨contestedOwner processed old.assigned p,hOwner p⟩
  let initial := initialLoopState table hne (fun p => inheritedPreferred inherited.assigned p.val)
  let localTable := domainTable view agent (fun p : contested => parent p.val) (fun p => whole p.val) target store table htable
  have herase : localTable.erase = table := domainTable_erase _ _ _ _ _ _ _ _
  have hlocalInitial := Local.initialLoopState_inherited localTable
    (fun i p => (strict_on_stored view store (parent p.val) (hstore.ordered _) (agent i)).monotoneOn)
    (fun p => hwhole p.val) hne (fun p => inheritedPreferred inherited.assigned p.val)
  change Local.Inherited localTable initial ∧ initial.selected.card ≤ Fintype.card contested at hlocalInitial
  obtain ⟨hInitialSemantic,hInitialRecords⟩ := inherited_from_domains view agent (fun p : contested => parent p.val)
    (fun p => whole p.val) target store table htable initial hlocalInitial.1
  have hOldEF : ∀ p q : contested,
      cachedValue agent (contestedOwner processed old.assigned p) q.val (old.point q.val) ≤
      cachedValue agent (contestedOwner processed old.assigned p) p.val (old.point p.val) := by
    intro p q
    let i : processed := ⟨contestedOwner processed old.assigned p,contestedOwner_mem processed old.assigned p⟩
    have hp : old.assigned i = p.val := contestedOwner_parent processed old.assigned p
    simpa only [ownValue,hp] using hbest i q.val
  have hOldTarget : ∀ p : contested, target (contestedOwner processed old.assigned p) ≤
      cachedValue agent (contestedOwner processed old.assigned p) p.val (old.point p.val) := by
    intro p
    let i : processed := ⟨contestedOwner processed old.assigned p,contestedOwner_mem processed old.assigned p⟩
    let q := favoriteUncontested processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) i.val
    have hp : old.assigned i = p.val := contestedOwner_parent processed old.assigned p
    have hq : old.point q = whole q := hunused q ((mem_uncontestedParents processed old.assigned q).mp
      (favoriteUncontested_spec processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) i.val).1)
    apply max_le
    · simpa only [ownValue,hp] using hbench i
    · simpa only [ownValue,hp,hq] using hbest i q
  have hsize : initial.selected.card + (Fintype.card contested-initial.selected.card) = Fintype.card contested :=
    Nat.add_sub_of_le hlocalInitial.2
  obtain ⟨after,final,trace,hexec,hafter,hext,hrecords,hcorrect,hfull,hselected⟩ := loop_success view baseline agent
    (fun p : contested => parent p.val) (fun p => whole p.val) target table (contestedOwner processed old.assigned) hOwner
    (fun p => old.point p.val) (fun p => holdCap p.val) hOldEF hOldTarget recurse oracle hcall _ store hstore
    (fun p => hwhole p.val) htable (fun p => hold p.val) initial hInitialRecords hInitialSemantic hsize prior
  have hforced : ∀ i, cachedValue agent i
      (favoriteUncontested processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) i)
      (whole (favoriteUncontested processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) i)) < benchmark i →
      i ∈ final.selected := by
    intro i hi
    apply hselected
    rcases hinput with ⟨hbelow,_⟩ | ⟨hInherited,hInheritedRecords,_⟩
    · exact ((not_lt_of_ge (hbelow i _)) hi).elim
    · have h := Local.high_benchmark_initial_selected (cachedValue agent) (domains view store parent) whole
        (fun i p => strict_on_stored view store (parent p) (hstore.ordered _) (agent i)) hwhole processed old.assigned hcard
        inherited.assigned inherited.point benchmark hInheritedRecords (fun i => (hInherited.1 i).2)
        hInherited.2.1 hInherited.2.2 localTable hne i hi
      exact h
  have hTableAfter := TableRecords.mono view agent (fun p : contested => parent p.val) (fun p => whole p.val) target hext table htable
  let localAfter := domainTable view agent (fun p : contested => parent p.val) (fun p => whole p.val) target after table hTableAfter
  have hLocalFinal := inherited_on_domains view agent (fun p : contested => parent p.val) (fun p => whole p.val) target after table
    hTableAfter final hcorrect hrecords
  let allocation := finishStage processed old.assigned hcard hstage (cachedValue agent) whole final hfull
  have hLocalAllocation := Local.finishStage_correct (cachedValue agent) (domains view after parent) whole
    (fun i p => (strict_on_stored view after (parent p) (hafter.ordered _) (agent i)).monotoneOn)
    (Records.mono view hext parent whole hwhole) processed old.assigned hcard hstage benchmark localAfter final
    hLocalFinal hfull hforced
  obtain ⟨hAllocation,hAllocationRecords⟩ := allocation_from_domains view agent parent whole benchmark after allocation hLocalAllocation
  let finish : Attempt GlobalParent Payload (LoopState Agent contested (OrderedRecord n)) →
      Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := fun returned =>
    match returned.2 with
    | none => .returned (returned.1,none)
    | some out => if hf : out.selected.card = Fintype.card contested then
        .returned (returned.1,some (finishStage processed old.assigned hcard hstage (cachedValue agent) whole out hf))
      else .returned (returned.1,none)
  have hreturn : Executes oracle (finish (after,some final)) (prior++trace) (after,some allocation) [] := by
    simp only [finish,dite_eq_left hfull]
    exact Executes.returned _ _
  have hjoined := hexec.bind finish hreturn
  rw [List.append_nil] at hjoined
  refine ⟨after,allocation,trace,?_,hafter,hext,hAllocationRecords,hAllocation⟩
  convert hjoined using 1 <;> dsimp only [stageProgram,finish,initial,hne,contested] <;> congr 2
  funext returned
  cases returned.2 <;> dsimp only <;> split_ifs <;> rfl

end EnvyFreeResearch.Full.Chores.SubCorePhysical
