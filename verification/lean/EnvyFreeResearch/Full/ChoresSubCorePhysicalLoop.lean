import EnvyFreeResearch.Full.ChoresSubCorePhysicalRefs
import EnvyFreeResearch.Full.ChoresSubCoreBudget

/-!
# Total finite physical selected-loop execution

The loop retains its store even when a smaller call reports failure. Its
termination, record references, and query ledger use no envy assumption.
The smaller-call premise is discharged by the population/fuel induction in
the physical driver, independently of the later success/replay proof.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem loop_executes
    (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (table : TrimTable (cachedValue agent) Set.univ whole target)
    (oldOwner : Parent ↪ Agent) (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Store GlobalParent Payload → Node selected Parent (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (Node selected Parent (OrderedRecord n))))
    (oracle : AdaptiveOracle.Policy Query ℝ) (isCut : Query → Bool) (queryBound cutBound : ℕ → ℕ)
    (hcall : ∀ selected : Finset Agent, selected.card < Fintype.card Parent →
      ∀ store, WellFormed view baseline store → ∀ before : Node selected Parent (OrderedRecord n),
      Records view store parent before.point → Records view store parent (table.remainingCap selected) →
      ∀ prior : OracleProtocol.History Query ℝ,
      ∃ out trace, Executes oracle (recurse selected store before) prior out trace ∧
        WellFormed view baseline out.1 ∧ Extends store out.1 ∧
        (∀ returned, out.2 = some returned → Records view out.1 parent returned.point) ∧
        trace.length ≤ queryBound selected.card ∧ trace.countP (fun qr => isCut qr.1) ≤ cutBound selected.card)
    (fuel : ℕ) (store : Store GlobalParent Payload) (hstore : WellFormed view baseline store)
    (hwhole : Records view store parent whole) (htable : TableRecords view agent parent whole target store table)
    (s : LoopState Agent Parent (OrderedRecord n)) (hs : Records view store parent s.node.point)
    (hsize : s.selected.card + fuel = Fintype.card Parent) (prior : OracleProtocol.History Query ℝ) :
    ∃ out trace, Executes oracle (loopProgram agent whole target table oldOwner hOwner recurse fuel store s) prior out trace ∧
      WellFormed view baseline out.1 ∧ Extends store out.1 ∧
      (∀ finished, out.2 = some finished → finished.selected.card = Fintype.card Parent ∧
        s.selected ⊆ finished.selected ∧ Records view out.1 parent finished.node.point) ∧
      trace.length ≤ loopBudget queryBound s.selected.card fuel ∧
      trace.countP (fun qr => isCut qr.1) ≤ loopBudget cutBound s.selected.card fuel := by
  induction fuel generalizing store s prior with
  | zero =>
    have hfull : s.selected.card = Fintype.card Parent := by omega
    refine ⟨(store, some s), [], ?_, hstore, Extends.refl store, ?_, Nat.zero_le _, Nat.zero_le _⟩
    · rw [loopProgram, ite_eq_left hfull]
      exact Executes.returned _ _
    · intro finished heq
      have heq' : s = finished := Option.some.inj heq
      subst finished
      exact ⟨hfull, Finset.Subset.refl _, hs⟩
  | succ fuel ih =>
    have hcard : s.selected.card < Fintype.card Parent := by omega
    have hnotfull : s.selected.card ≠ Fintype.card Parent := Nat.ne_of_lt hcard
    obtain ⟨first, firstTrace, hfirst, hFirstStore, hFirstExt, hFirstRecords, hFirstQ, hFirstC⟩ :=
      hcall s.selected hcard store hstore s.node hs (cap_records view agent parent whole target store table htable hwhole _) prior
    cases hresult : first.2 with
    | none =>
      have hreturn : Executes oracle
          (match first.2 with
          | none => Program.returned (first.1, none)
          | some node => loopProgram agent whole target table oldOwner hOwner recurse fuel first.1
              (nextLoopState table oldOwner hOwner s.selected hcard node))
          (prior ++ firstTrace) (first.1, none) [] := by
        rw [hresult]
        exact Executes.returned _ _
      have hjoined := hfirst.bind (fun returned => match returned.2 with
        | none => Program.returned (returned.1, none)
        | some node => loopProgram agent whole target table oldOwner hOwner recurse fuel returned.1
            (nextLoopState table oldOwner hOwner s.selected hcard node)) hreturn
      rw [List.append_nil] at hjoined
      refine ⟨(first.1, none), firstTrace, ?_, hFirstStore, hFirstExt, ?_, ?_, ?_⟩
      · rw [loopProgram, ite_eq_right hnotfull, dite_eq_left hcard]
        exact hjoined
      · intro finished heq
        cases heq
      · rw [loopBudget]
        exact hFirstQ.trans (Nat.le_add_right _ _)
      · rw [loopBudget]
        exact hFirstC.trans (Nat.le_add_right _ _)
    | some returned =>
      let next := nextLoopState table oldOwner hOwner s.selected hcard returned
      have hWhole' : Records view first.1 parent whole := Records.mono view hFirstExt parent whole hwhole
      have hTable' : TableRecords view agent parent whole target first.1 table :=
        TableRecords.mono view agent parent whole target hFirstExt table htable
      have hNextRecords : Records view first.1 parent next.node.point := next_records view agent parent whole target
        first.1 table hTable' hWhole' oldOwner hOwner s.selected hcard returned (hFirstRecords returned hresult)
      have hNextCard : next.selected.card = s.selected.card + 1 := nextLoopState_card table oldOwner hOwner s.selected hcard returned
      have hNextSize : next.selected.card + fuel = Fintype.card Parent := by omega
      obtain ⟨out, tail, htail, hout, hext, hfinish, hTailQ, hTailC⟩ :=
        ih first.1 hFirstStore hWhole' hTable' next hNextRecords hNextSize (prior ++ firstTrace)
      have hjoined := hfirst.bind (fun returned => match returned.2 with
        | none => Program.returned (returned.1, none)
        | some node => loopProgram agent whole target table oldOwner hOwner recurse fuel returned.1
            (nextLoopState table oldOwner hOwner s.selected hcard node))
        (by simpa only [hresult] using htail)
      refine ⟨out, firstTrace ++ tail, ?_, hout, hFirstExt.trans hext, ?_, ?_, ?_⟩
      · rw [loopProgram, ite_eq_right hnotfull, dite_eq_left hcard]
        exact hjoined
      · intro finished heq
        obtain ⟨hfull, hsub, hrecords⟩ := hfinish finished heq
        exact ⟨hfull, (nextLoopState_contains table oldOwner hOwner s.selected hcard returned).trans hsub, hrecords⟩
      · rw [List.length_append, loopBudget]
        rw [hNextCard] at hTailQ
        exact Nat.add_le_add hFirstQ hTailQ
      · rw [List.countP_append, loopBudget]
        rw [hNextCard] at hTailC
        exact Nat.add_le_add hFirstC hTailC

end EnvyFreeResearch.Full.Chores.SubCorePhysical
