import EnvyFreeResearch.Full.ChoresSubCorePhysicalTrims
import EnvyFreeResearch.Full.ChoresSubCorePhysicalProgram

/-!
# Record references retained by every query-free SubCore transition

These invariants require no envy hypothesis. They ensure all later targets
are computed from immutable cached records and all recursive offered caps
remain physical records in the persistent global table.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set Persistent SubCore

variable {n : ℕ} {GlobalParent Payload Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]
    (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))

def TableRecords (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target) : Prop :=
  ∀ i p r, table.endpoint i p = some r → Stored view store (parent p) r

theorem TableRecords.mono {before after : Store GlobalParent Payload}
    (h : Extends before after) (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target before table) :
    TableRecords view agent parent whole target after table :=
  fun i p r hr => Stored.mono view h (ht i p r hr)

theorem table_point_records (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target store table)
    (i : Agent) (p : Parent) (hi : i ∈ table.available p) : Stored view store (parent p) (table.point i p) := by
  have hs : (table.endpoint i p).isSome := (Finset.mem_filter.mp hi).2
  cases heq : table.endpoint i p with
  | none => simp only [heq, Option.isSome_none, Bool.false_eq_true] at hs
  | some r => simpa only [TrimTable.point, heq, Option.getD_some] using ht i p r heq

theorem winner_records (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target store table)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    Records view store parent (fun p => table.point (table.winner hne preferred p) p) :=
  fun p => table_point_records view agent parent whole target store table ht _ p (table.winner_spec hne preferred p).1

theorem cap_records (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target store table) (hw : Records view store parent whole)
    (selected : Finset Agent) : Records view store parent (table.remainingCap selected) := by
  intro p
  by_cases hrem : (table.remaining selected p).Nonempty
  · obtain ⟨i, hi, _, heq, _⟩ := table.cap_attained selected p hrem
    rw [heq]
    exact table_point_records view agent parent whole target store table ht i p hi
  · rw [table.cap_whole_of_empty selected p hrem]
    exact hw p

theorem refresh_records (store : Store GlobalParent Payload) (selected : Finset Agent)
    (assigned : selected ↪ Parent) (point cap : Parent → OrderedRecord n)
    (hp : Records view store parent point) (hc : Records view store parent cap) :
    Records view store parent (refreshUnused selected assigned point cap) := by
  classical
  intro p
  unfold refreshUnused
  split_ifs
  · exact hp p
  · exact hc p

theorem initial_records (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target store table) (hw : Records view store parent whole)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    Records view store parent (initialLoopState table hne preferred).node.point :=
  refresh_records view parent store _ _ _ _ (winner_records view agent parent whole target store table ht hne preferred)
    (cap_records view agent parent whole target store table ht hw _)

theorem next_records (store : Store GlobalParent Payload)
    (table : TrimTable (cachedValue agent) Set.univ whole target)
    (ht : TableRecords view agent parent whole target store table) (hw : Records view store parent whole)
    (oldOwner : Parent ↪ Agent) (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (returned : Node selected Parent (OrderedRecord n)) (hr : Records view store parent returned.point) :
    Records view store parent (nextLoopState table oldOwner hOwner selected hcard returned).node.point :=
  refresh_records view parent store _ _ _ _ hr (cap_records view agent parent whole target store table ht hw _)

theorem extended_records (store : Store GlobalParent Payload) (contested : Finset Parent)
    (point : contested → OrderedRecord n)
    (hp : Records view store (fun p : contested => parent p.val) point)
    (hw : Records view store parent whole) : Records view store parent (extendPoint contested point whole) := by
  intro p
  by_cases hmem : p ∈ contested
  · rw [show extendPoint contested point whole p = point ⟨p, hmem⟩ from extendPoint_inside contested point whole ⟨p, hmem⟩]
    exact hp ⟨p, hmem⟩
  · rw [extendPoint_outside contested point whole p hmem]
    exact hw p

theorem finish_records (store : Store GlobalParent Payload)
    (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card + 1 = Fintype.card Agent)
    (out : LoopState Agent (contestedParents processed oldAssignment) (OrderedRecord n))
    (hfull : out.selected.card = Fintype.card (contestedParents processed oldAssignment))
    (hp : Records view store (fun p : contestedParents processed oldAssignment => parent p.val) out.node.point)
    (hw : Records view store parent whole) :
    Records view store parent (finishStage processed oldAssignment hcard hstage (cachedValue agent) whole out hfull).point :=
  extended_records view parent whole store _ _ hp hw

end EnvyFreeResearch.Full.Chores.SubCorePhysical
