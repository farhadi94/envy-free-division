import EnvyFreeResearch.Full.ChoresSubCorePhysicalExecution
import EnvyFreeResearch.Full.ChoresSubCoreLocalStage
import EnvyFreeResearch.Full.ChoresSubCoreNonnegative

/-! Successful execution of the physical selected-set loop from actual
smaller calls. Domain-local strictness is derived from each returned store;
no external fair-allocation oracle or analytic replay is assumed. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set QueryProgram Persistent SubCore
variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem loop_success
    (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (table : TrimTable (cachedValue agent) univ whole target)
    (oldOwner : Parent ↪ Agent) (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (old : Parent → OrderedRecord n) (holdCap : ∀ p, old p ≤ whole p)
    (hOldEF : ∀ p q, cachedValue agent (oldOwner p) q (old q) ≤ cachedValue agent (oldOwner p) p (old p))
    (hOldTarget : ∀ p, target (oldOwner p) ≤ cachedValue agent (oldOwner p) p (old p))
    (recurse : ∀ selected : Finset Agent, Store GlobalParent Payload → Node selected Parent (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (Node selected Parent (OrderedRecord n))))
    (oracle : AdaptiveOracle.Policy Query ℝ)
    (hcall : ∀ selected : Finset Agent, selected.card < Fintype.card Parent →
      ∀ store, WellFormed view baseline store → ∀ before : Node selected Parent (OrderedRecord n),
      Records view store parent before.point → Records view store parent (table.remainingCap selected) →
      SubCore.Inherited table ⟨selected,before⟩ → ∀ prior : OracleProtocol.History Query ℝ,
      ∃ after returned trace, Executes oracle (recurse selected store before) prior (after,some returned) trace ∧
        WellFormed view baseline after ∧ Extends store after ∧ Records view after parent returned.point ∧
        SubCore.RecursiveCorrect table selected before returned)
    (fuel : ℕ) (store : Store GlobalParent Payload) (hstore : WellFormed view baseline store)
    (hwhole : Records view store parent whole) (htable : TableRecords view agent parent whole target store table)
    (hold : Records view store parent old)
    (s : LoopState Agent Parent (OrderedRecord n)) (hs : Records view store parent s.node.point)
    (hsemantic : SubCore.Inherited table s)
    (hsize : s.selected.card + fuel = Fintype.card Parent) (prior : OracleProtocol.History Query ℝ) :
    ∃ after out trace, Executes oracle (loopProgram agent whole target table oldOwner hOwner recurse fuel store s)
        prior (after,some out) trace ∧
      WellFormed view baseline after ∧ Extends store after ∧ Records view after parent out.node.point ∧
      SubCore.Inherited table out ∧ out.selected.card = Fintype.card Parent ∧ s.selected ⊆ out.selected := by
  induction fuel generalizing store s prior with
  | zero =>
    have hfull : s.selected.card = Fintype.card Parent := by omega
    refine ⟨store,s,[],?_,hstore,Extends.refl store,hs,hsemantic,hfull,Finset.Subset.refl _⟩
    rw [loopProgram,ite_eq_left hfull]
    exact Executes.returned _ _
  | succ fuel ih =>
    have hcard : s.selected.card < Fintype.card Parent := by omega
    have hnotfull : s.selected.card ≠ Fintype.card Parent := Nat.ne_of_lt hcard
    obtain ⟨first,returned,firstTrace,hfirst,hFirstStore,hFirstExt,hFirstRecords,hFirstCorrect⟩ :=
      hcall s.selected hcard store hstore s.node hs
        (cap_records view agent parent whole target store table htable hwhole _) hsemantic prior
    have hWhole' := Records.mono view hFirstExt parent whole hwhole
    have hTable' := TableRecords.mono view agent parent whole target hFirstExt table htable
    have hOld' := Records.mono view hFirstExt parent old hold
    let localTable := domainTable view agent parent whole target first table hTable'
    have hlocal : Local.Inherited localTable
        (nextLoopState localTable.erase oldOwner hOwner s.selected hcard returned) :=
      Local.nextLoopState_inherited localTable oldOwner hOwner
        (fun i p => strict_on_stored view first (parent p) (hFirstStore.ordered _) (agent i))
        hWhole' old hOld' holdCap hOldEF hOldTarget s.selected hcard s.node returned
        (inherited_on_domains view agent parent whole target first table hTable' s hsemantic
          (Records.mono view hFirstExt parent s.node.point hs))
        (recursive_on_domains view agent parent whole target first table hTable' s.selected s.node returned
          hFirstCorrect hFirstRecords)
    have herase : localTable.erase = table := domainTable_erase view agent parent whole target first table hTable'
    change Local.Inherited localTable (nextLoopState table oldOwner hOwner s.selected hcard returned) at hlocal
    obtain ⟨hNextSemantic,hNextRecords⟩ := inherited_from_domains view agent parent whole target first table hTable'
      (nextLoopState table oldOwner hOwner s.selected hcard returned) hlocal
    let next := nextLoopState table oldOwner hOwner s.selected hcard returned
    have hNextSize : next.selected.card + fuel = Fintype.card Parent := by
      have hc := nextLoopState_card table oldOwner hOwner s.selected hcard returned
      change next.selected.card = s.selected.card+1 at hc
      omega
    obtain ⟨after,out,tail,htail,hafter,hext,hrecords,hcorrect,hfull,hsub⟩ :=
      ih first hFirstStore hWhole' hTable' hOld' next hNextRecords hNextSemantic hNextSize (prior++firstTrace)
    have hjoined := hfirst.bind (fun result => match result.2 with
      | none => Program.returned (result.1,none)
      | some node => loopProgram agent whole target table oldOwner hOwner recurse fuel result.1
          (nextLoopState table oldOwner hOwner s.selected hcard node)) htail
    refine ⟨after,out,firstTrace++tail,?_,hafter,hFirstExt.trans hext,hrecords,hcorrect,hfull,?_⟩
    · rw [loopProgram,ite_eq_right hnotfull,dite_eq_left hcard]
      exact hjoined
    · exact (nextLoopState_contains table oldOwner hOwner s.selected hcard returned).trans hsub

end EnvyFreeResearch.Full.Chores.SubCorePhysical
