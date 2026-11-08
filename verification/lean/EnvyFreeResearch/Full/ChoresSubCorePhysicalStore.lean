import EnvyFreeResearch.Full.ChoresSubCoreRecordOrder
import EnvyFreeResearch.Full.ChoresSubCoreSelection
import EnvyFreeResearch.Full.ChoresSuffixLookup

/-!
# Stateful physical SubCore records and trim tables

The store retains the complete payload, including unclipped raw rows when
present. SubCore coordinates project only the immutable cached Record. The
leaf operation is an ordinary-query suffix recorder; no fair-allocation
operation is assumed. Every new table threads all prior store updates.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*}

abbrev Store (GlobalParent Payload : Type*) := GlobalParent → List Payload

def Extends (before after : Store GlobalParent Payload) : Prop := ∀ p, (before p).Sublist (after p)

def Stored (view : Payload → Record n) (store : Store GlobalParent Payload) (p : GlobalParent)
    (r : OrderedRecord n) : Prop := ∃ payload ∈ store p, view payload = r.record

structure EnsureOutput (GlobalParent Payload : Type*) (n : ℕ) where
  store : Store GlobalParent Payload
  endpoint : OrderedRecord n

variable [DecidableEq GlobalParent]

def ensureGlobalProgram (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (store : Store GlobalParent Payload) (p : GlobalParent) (i : Fin n) (target : Lex (ℝ × ℚ)) :
    Program Query ℝ (EnsureOutput GlobalParent Payload n) :=
  (ensure p i (ofLex target) (store p)).bind (fun out =>
    .returned ⟨Function.update store p out.records, orderedRecord (view out.selected)⟩)

/-- The global recorder preserves the exact leaf trace and all immutable
records. Its premise is a concrete leaf execution, not a fairness interface. -/
theorem ensure_global_executes (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (oracle : AdaptiveOracle.Policy Query ℝ) (store : Store GlobalParent Payload)
    (p : GlobalParent) (i : Fin n) (target : Lex (ℝ × ℚ))
    (out : Suffix.Lookup.Result Payload) (prior trace : OracleProtocol.History Query ℝ)
    (hexec : Executes oracle (ensure p i (ofLex target) (store p)) prior out trace)
    (hpersist : (store p).Sublist out.records) (hselected : out.selected ∈ out.records)
    (htarget : (view out.selected).formal i = ofLex target) :
    let result : EnsureOutput GlobalParent Payload n := ⟨Function.update store p out.records, orderedRecord (view out.selected)⟩
    Executes oracle (ensureGlobalProgram view ensure store p i target) prior result trace ∧
      Extends store result.store ∧ Stored view result.store p result.endpoint ∧ formalValue i result.endpoint = target := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hexec.bind (fun out => Program.returned
      (⟨Function.update store p out.records, orderedRecord (view out.selected)⟩ : EnsureOutput GlobalParent Payload n))
      (Executes.returned _ (prior ++ trace))
    simpa only [ensureGlobalProgram, List.append_nil] using h
  · intro q
    by_cases hq : q = p
    · subst q
      simpa only [Function.update_self] using hpersist
    · simpa only [Function.update_of_ne hq] using (List.Sublist.refl (store q))
  · exact ⟨out.selected, by simpa only [Function.update_self] using hselected, rfl⟩
  · exact congrArg toLex htarget

variable [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

abbrev cachedValue (agent : Agent → Fin n) (i : Agent) (_ : Parent) (r : OrderedRecord n) : Lex (ℝ × ℚ) :=
  formalValue (agent i) r

def RecordRowSpec (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (pair : Agent × Parent) (reply : Option (OrderedRecord n)) : Prop :=
  match reply with
  | none => formalValue (agent pair.1) (whole pair.2) < target pair.1
  | some r => r ≤ whole pair.2 ∧ formalValue (agent pair.1) r = target pair.1 ∧
      target pair.1 ≤ formalValue (agent pair.1) (whole pair.2)

structure OneTrimOutput (GlobalParent Payload : Type*) (n : ℕ) where
  store : Store GlobalParent Payload
  endpoint : Option (OrderedRecord n)

def oneTrimProgram (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (store : Store GlobalParent Payload) (pair : Agent × Parent) :
    Program Query ℝ (OneTrimOutput GlobalParent Payload n) := by
  classical
  exact if formalValue (agent pair.1) (whole pair.2) < target pair.1 then .returned ⟨store, none⟩ else
    (ensureGlobalProgram view ensure store (parent pair.2) (agent pair.1) (target pair.1)).bind
      (fun out => .returned ⟨out.store, some out.endpoint⟩)

structure TrimRows (GlobalParent Payload Agent Parent : Type*) (n : ℕ) where
  store : Store GlobalParent Payload
  rows : Agent × Parent → Option (OrderedRecord n)

def trimListProgram (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) :
    List (Agent × Parent) → Store GlobalParent Payload → Program Query ℝ (TrimRows GlobalParent Payload Agent Parent n)
  | [], store => .returned ⟨store, fun _ => none⟩
  | pair :: rest, store => (oneTrimProgram view ensure agent parent whole target store pair).bind (fun first =>
      (trimListProgram view ensure agent parent whole target rest first.store).bind (fun tail =>
        .returned ⟨tail.store, Function.update tail.rows pair first.endpoint⟩))

def tableFromRows (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (rows : Agent × Parent → Option (OrderedRecord n))
    (hrows : ∀ pair, RecordRowSpec agent whole target pair (rows pair)) :
    TrimTable (cachedValue agent) Set.univ whole target := by
  refine ⟨fun i p => rows (i, p), ?_, ?_⟩
  · intro i p
    have h := hrows (i, p)
    cases heq : rows (i, p) with
    | none =>
      rw [heq] at h
      exact ⟨fun _ => h, fun _ => rfl⟩
    | some r =>
      rw [heq] at h
      constructor
      · intro hbad
        cases hbad
      · intro hbad
        exact ((not_lt_of_ge h.2.2) hbad).elim
  · intro i p r hr
    have h := hrows (i, p)
    rw [hr] at h
    exact ⟨Set.mem_univ _, h.1, h.2.1⟩

def trimTableProgram (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (store : Store GlobalParent Payload) :
    Program Query ℝ (Store GlobalParent Payload × Option (TrimTable (cachedValue agent) Set.univ whole target)) := by
  classical
  exact if ∀ i, 0 ≤ (ofLex (target i)).1 then
    (trimListProgram view ensure agent parent whole target Finset.univ.toList store).bind (fun out =>
      if hrows : ∀ pair, RecordRowSpec agent whole target pair (out.rows pair) then
        .returned (out.store, some (tableFromRows agent whole target out.rows hrows)) else .returned (out.store, none))
    else .returned (store, none)

end EnvyFreeResearch.Full.Chores.SubCorePhysical
