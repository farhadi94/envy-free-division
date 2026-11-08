import EnvyFreeResearch.Full.ChoresSubCorePhysicalStore
import EnvyFreeResearch.Full.ChoresSubCoreStage

/-!
# Stateful physical SubCore recursion

This program uses only immutable cached formal rows and the supplied physical
suffix recorder. Complete payload stores survive every recursive call and
every checked failure. In particular, clipped raw values are retained and
exploratory records are never rolled back. Correctness and replay to the
closed strict-source program are proved separately.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

variable {n : ℕ} {GlobalParent Payload Query : Type*} [DecidableEq GlobalParent]

abbrev Attempt (GlobalParent Payload Result : Type*) := Store GlobalParent Payload × Option Result

variable {Agent Parent : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

def emptyRecordNode (selected : Finset Agent) (hzero : selected.card = 0)
    (whole : Parent → OrderedRecord n) : Node selected Parent (OrderedRecord n) := by
  have hnone : ∀ i : selected, False := by
    intro i
    have hpositive := Finset.card_pos.mpr ⟨i.val, i.property⟩
    omega
  exact ⟨⟨fun i => (hnone i).elim, fun i _ _ => (hnone i).elim⟩, whole⟩

def loopProgram (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (table : TrimTable (cachedValue agent) Set.univ whole target)
    (oldOwner : Parent ↪ Agent) (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Store GlobalParent Payload → Node selected Parent (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (Node selected Parent (OrderedRecord n)))) :
    ℕ → Store GlobalParent Payload → LoopState Agent Parent (OrderedRecord n) →
      Program Query ℝ (Attempt GlobalParent Payload (LoopState Agent Parent (OrderedRecord n)))
  | fuel, store, s => if s.selected.card = Fintype.card Parent then .returned (store, some s) else
      match fuel with
      | 0 => .returned (store, none)
      | fuel + 1 => if hcard : s.selected.card < Fintype.card Parent then
          (recurse s.selected store s.node).bind (fun returned => match returned.2 with
            | none => .returned (returned.1, none)
            | some node => loopProgram agent whole target table oldOwner hOwner recurse fuel returned.1
                (nextLoopState table oldOwner hOwner s.selected hcard node))
        else .returned (store, none)

def stageProgram (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
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
    (store : Store GlobalParent Payload) : Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := by
  classical
  let hne : ∀ p, (table.available p).Nonempty := fun p => ⟨contestedOwner processed old.assigned p, hOwner p⟩
  let initial := initialLoopState table hne (fun p => inheritedPreferred inherited.assigned p.val)
  exact (loopProgram agent (fun p => whole p.val) _ table (contestedOwner processed old.assigned) hOwner recurse
    (Fintype.card (contestedParents processed old.assigned) - initial.selected.card) store initial).bind (fun returned =>
      match returned.2 with
      | none => .returned (returned.1, none)
      | some out => if hfull : out.selected.card = Fintype.card (contestedParents processed old.assigned) then
          .returned (returned.1, some (finishStage processed old.assigned hcard hstage (cachedValue agent) whole out hfull))
        else .returned (returned.1, none))

universe u v

def recursiveProgram (fuel : ℕ) (Agent : Type u) (Parent : Type v)
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]
    (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (benchmark : Agent → Lex (ℝ × ℚ)) (inherited : Allocation Agent Parent (OrderedRecord n))
    (store : Store GlobalParent Payload) : Program Query ℝ (Attempt GlobalParent Payload (Allocation Agent Parent (OrderedRecord n))) := by
  classical
  exact match fuel with
  | 0 => .returned (store, none)
  | fuel + 1 => if hpositive : 0 < Fintype.card Agent then
      let newAgent : Agent := Classical.choice (Fintype.card_pos_iff.mp hpositive)
      let processed : Finset Agent := Finset.univ.erase newAgent
      let hstage : processed.card + 1 = Fintype.card Agent := by
        simpa only [processed, Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ newAgent)
      let oldProgram : Program Query ℝ (Attempt GlobalParent Payload (Node processed Parent (OrderedRecord n))) :=
        if hzero : processed.card = 0 then .returned (store, some (emptyRecordNode processed hzero whole)) else
          (recursiveProgram fuel processed Parent view ensure (fun i : processed => agent i.val) parent whole
            (fun i : processed => benchmark i.val)
            ⟨(⟨Subtype.val, Subtype.val_injective⟩ : processed ↪ Agent).trans inherited.assigned, inherited.point⟩ store).bind
            (fun out => .returned (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩)))
      oldProgram.bind (fun previous => match previous.2 with
        | none => .returned (previous.1, none)
        | some old => if hcard : processed.card < Fintype.card Parent then
            let contested := contestedParents processed old.assigned
            let target := stageTarget processed old.assigned hcard (fun i p => cachedValue agent i p (whole p)) benchmark
            (trimTableProgram view ensure agent (fun p : contested => parent p.val) (fun p => whole p.val) target previous.1).bind
              (fun prepared => match prepared.2 with
                | none => .returned (prepared.1, none)
                | some table => if hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p then
                    stageProgram agent whole processed old hcard hstage inherited benchmark table hOwner
                      (fun selected current before => if hzero : selected.card = 0 then
                        .returned (current, some (emptyRecordNode selected hzero (table.remainingCap selected)))
                      else (recursiveProgram fuel selected contested view ensure (fun i : selected => agent i.val)
                        (fun p : contested => parent p.val) (table.remainingCap selected)
                        (ownValue selected before (fun i (p : contested) => cachedValue agent i p.val))
                        ⟨before.assigned, before.point⟩ current).bind
                        (fun out => .returned (out.1, out.2.map (fun allocation => ⟨allocation.assigned, allocation.point⟩)))) prepared.1
                  else .returned (prepared.1, none))
          else .returned (previous.1, none))
    else .returned (store, none)
termination_by fuel

end EnvyFreeResearch.Full.Chores.SubCorePhysical
