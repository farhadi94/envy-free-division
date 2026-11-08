import EnvyFreeResearch.Full.ChoresSubCorePhysicalRefs
import EnvyFreeResearch.Full.ChoresSubCoreLocalAllocation

/-! Exact semantics on retained physical records. Each parent has its own
feasible domain; no global monotonicity of arbitrary record vectors is used. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical
open Set Persistent SubCore
variable {n : ℕ} {GlobalParent Payload Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]
    [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

def domains (view : Payload → Record n) (store : Store GlobalParent Payload)
    (parent : Parent → GlobalParent) (p : Parent) : Set (OrderedRecord n) :=
  {r | Stored view store (parent p) r}

theorem strict_on_stored (view : Payload → Record n) (store : Store GlobalParent Payload)
    (p : GlobalParent) (horder : (store p).Pairwise (fun r s => Before (view r) (view s))) (i : Fin n) :
    StrictMonoOn (formalValue i) {r | Stored view store p r} := by
  intro r hr s hs hrs
  apply lt_of_not_ge
  intro hbad
  exact (not_le_of_gt hrs) (stored_formal_le_coord view store p horder i s r hs hr hbad)

def domainTable (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (table : SubCore.TrimTable (cachedValue agent) univ whole target)
    (ht : TableRecords view agent parent whole target store table) :
    Local.TrimTable (cachedValue agent) (domains view store parent) whole target :=
  ⟨table.endpoint, table.unavailable, fun i p r hr => ⟨ht i p r hr, (table.legal i p r hr).2⟩⟩

@[simp] theorem domainTable_erase (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (table : SubCore.TrimTable (cachedValue agent) univ whole target)
    (ht : TableRecords view agent parent whole target store table) :
    (domainTable view agent parent whole target store table ht).erase = table := by
  cases table
  rfl

theorem inherited_on_domains (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (table : SubCore.TrimTable (cachedValue agent) univ whole target)
    (ht : TableRecords view agent parent whole target store table) (s : LoopState Agent Parent (OrderedRecord n))
    (hs : SubCore.Inherited table s) (hr : Records view store parent s.node.point) :
    Local.Inherited (domainTable view agent parent whole target store table ht) s :=
  ⟨fun p => ⟨hr p, (hs.1 p).2⟩, hs.2⟩

theorem inherited_from_domains (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (table : SubCore.TrimTable (cachedValue agent) univ whole target)
    (ht : TableRecords view agent parent whole target store table) (s : LoopState Agent Parent (OrderedRecord n))
    (hs : Local.Inherited (domainTable view agent parent whole target store table ht) s) :
    SubCore.Inherited table s ∧ Records view store parent s.node.point :=
  ⟨⟨fun p => ⟨Set.mem_univ _, (hs.1 p).2⟩, hs.2⟩, fun p => (hs.1 p).1⟩

theorem recursive_on_domains (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (target : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (table : SubCore.TrimTable (cachedValue agent) univ whole target)
    (ht : TableRecords view agent parent whole target store table) (selected : Finset Agent)
    (before returned : Node selected Parent (OrderedRecord n))
    (hs : SubCore.RecursiveCorrect table selected before returned) (hr : Records view store parent returned.point) :
    Local.RecursiveCorrect (domainTable view agent parent whole target store table ht) selected before returned :=
  ⟨fun p => ⟨hr p, (hs.1 p).2⟩, hs.2⟩

theorem allocation_from_domains (view : Payload → Record n) (agent : Agent → Fin n) (parent : Parent → GlobalParent)
    (whole : Parent → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (out : Allocation Agent Parent (OrderedRecord n))
    (hs : Local.AllocationCorrect (cachedValue agent) (domains view store parent) whole benchmark out) :
    SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out ∧ Records view store parent out.point :=
  ⟨⟨fun p => ⟨Set.mem_univ _, (hs.1 p).2⟩, hs.2⟩, fun p => (hs.1 p).1⟩

end EnvyFreeResearch.Full.Chores.SubCorePhysical
