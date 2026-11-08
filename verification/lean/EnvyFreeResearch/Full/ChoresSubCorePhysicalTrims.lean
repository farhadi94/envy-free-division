import EnvyFreeResearch.Full.ChoresSubCoreRecordFacts

/-!
# Executing physical trim tables from concrete suffix-recorder contracts

The only leaf premise is exact target recording with persistent ordered rows
and an ordinary-query ledger. No allocation or envy conclusion occurs in it.
These compositional theorems are used with the proved affine/clipped recorders.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Set QueryProgram Persistent SubCore

/- The concrete instantiation includes original-measure soundness, physical
coordinate bounds, and any retained raw-value information. Keeping this
predicate in the invariant prevents an exact-recorder contract from being
mistakenly required to work on arbitrary fictitious cached cost rows. -/
class RecordValidity (GlobalParent Payload : Type*) where
  valid : GlobalParent → Payload → Prop
  storeValid : Store GlobalParent Payload → Prop

variable {n : ℕ} {GlobalParent Payload Query Agent Parent : Type*} [DecidableEq GlobalParent]
    [RecordValidity GlobalParent Payload]

structure WellFormed (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) : Prop where
  ordered : ∀ p, (store p).Pairwise (fun r s => Before (view r) (view s))
  lower : ∀ p r, r ∈ store p → ∀ i, baseline i ≤ toLex ((view r).formal i)
  valid : ∀ p r, r ∈ store p → RecordValidity.valid p r
  store_valid : RecordValidity.storeValid store

def Records (view : Payload → Record n) (store : Store GlobalParent Payload)
    (parent : Parent → GlobalParent) (point : Parent → OrderedRecord n) : Prop :=
  ∀ p, Stored view store (parent p) (point p)

theorem Records.mono (view : Payload → Record n) {before after : Store GlobalParent Payload}
    (h : Extends before after) (parent : Parent → GlobalParent) (point : Parent → OrderedRecord n)
    (hp : Records view before parent point) : Records view after parent point :=
  fun p => (hp p).mono view h

theorem record_baseline_le (view : Payload → Record n) (baseline : Fin n → Lex (ℝ × ℚ))
    (store : Store GlobalParent Payload) (hstore : WellFormed view baseline store)
    (p : GlobalParent) (r : OrderedRecord n) (hr : Stored view store p r) (i : Fin n) :
    baseline i ≤ formalValue i r := by
  obtain ⟨payload, hpayload, heq⟩ := hr
  change baseline i ≤ toLex (r.record.formal i)
  rw [← heq]
  exact hstore.lower p payload hpayload i

/-- The physical suffix-recorder contract, stated on its actual query
program. The cap is an existing physical record and the target is both
formally above the common baseline and physically nonnegative. -/
def RecordsTargets (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound : ℕ) : Prop :=
  ∀ store, WellFormed view baseline store → ∀ p i target cap,
    Stored view store p cap → baseline i ≤ target → 0 ≤ (ofLex target).1 → target ≤ formalValue i cap →
    ∀ prior : OracleProtocol.History Query ℝ,
    ∃ out trace, Executes oracle (ensureGlobalProgram view ensure store p i target) prior out trace ∧
      WellFormed view baseline out.store ∧ Extends store out.store ∧
      Stored view out.store p out.endpoint ∧ formalValue i out.endpoint = target ∧
      trace.length ≤ freshQueryBound ∧ trace.countP (fun qr => isCut qr.1) ≤ 1

def OptionStored (view : Payload → Record n) (store : Store GlobalParent Payload) (p : GlobalParent) :
    Option (OrderedRecord n) → Prop
  | none => True
  | some r => Stored view store p r

theorem OptionStored.mono (view : Payload → Record n) {before after : Store GlobalParent Payload}
    (h : Extends before after) (p : GlobalParent) (point : Option (OrderedRecord n))
    (hp : OptionStored view before p point) : OptionStored view after p point := by
  cases point with
  | none => trivial
  | some r => exact Stored.mono view h hp

variable [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem one_trim_executes (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound : ℕ)
    (hEnsure : RecordsTargets view ensure baseline oracle isCut freshQueryBound)
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (store : Store GlobalParent Payload)
    (hstore : WellFormed view baseline store) (hwhole : Records view store parent whole)
    (hlow : ∀ i, baseline (agent i) ≤ target i) (hnonneg : ∀ i, 0 ≤ (ofLex (target i)).1)
    (pair : Agent × Parent) (prior : OracleProtocol.History Query ℝ) :
    ∃ out trace, Executes oracle (oneTrimProgram view ensure agent parent whole target store pair) prior out trace ∧
      WellFormed view baseline out.store ∧ Extends store out.store ∧
      RecordRowSpec agent whole target pair out.endpoint ∧ OptionStored view out.store (parent pair.2) out.endpoint ∧
      trace.length ≤ freshQueryBound ∧ trace.countP (fun qr => isCut qr.1) ≤ 1 := by
  classical
  by_cases hsmall : formalValue (agent pair.1) (whole pair.2) < target pair.1
  · refine ⟨⟨store, none⟩, [], ?_, hstore, Extends.refl store, hsmall, trivial, Nat.zero_le _, by simp⟩
    rw [oneTrimProgram, ite_eq_left hsmall]
    exact Executes.returned _ _
  · obtain ⟨out, trace, hexec, hout, hext, hrecord, htarget, hQ, hC⟩ := hEnsure store hstore
      (parent pair.2) (agent pair.1) (target pair.1) (whole pair.2) (hwhole pair.2)
      (hlow pair.1) (hnonneg pair.1) (le_of_not_gt hsmall) prior
    have hcap : out.endpoint ≤ whole pair.2 := stored_formal_le_coord view out.store (parent pair.2)
      (hout.ordered _) (agent pair.1) out.endpoint (whole pair.2) hrecord ((hwhole pair.2).mono view hext)
      (htarget.le.trans (le_of_not_gt hsmall))
    let result : OneTrimOutput GlobalParent Payload n := ⟨out.store, some out.endpoint⟩
    have hjoined := hexec.bind (fun out => Program.returned (⟨out.store, some out.endpoint⟩ : OneTrimOutput GlobalParent Payload n))
      (Executes.returned result (prior ++ trace))
    rw [List.append_nil] at hjoined
    refine ⟨result, trace, ?_, hout, hext, ⟨hcap, htarget, le_of_not_gt hsmall⟩, hrecord, hQ, hC⟩
    simpa only [oneTrimProgram, ite_eq_right hsmall] using hjoined

theorem trim_list_executes (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound : ℕ)
    (hEnsure : RecordsTargets view ensure baseline oracle isCut freshQueryBound)
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (hlow : ∀ i, baseline (agent i) ≤ target i)
    (hnonneg : ∀ i, 0 ≤ (ofLex (target i)).1)
    (pairs : List (Agent × Parent)) (store : Store GlobalParent Payload)
    (hstore : WellFormed view baseline store) (hwhole : Records view store parent whole)
    (prior : OracleProtocol.History Query ℝ) :
    ∃ out trace, Executes oracle (trimListProgram view ensure agent parent whole target pairs store) prior out trace ∧
      WellFormed view baseline out.store ∧ Extends store out.store ∧
      (∀ pair ∈ pairs, RecordRowSpec agent whole target pair (out.rows pair)) ∧
      (∀ pair ∈ pairs, OptionStored view out.store (parent pair.2) (out.rows pair)) ∧
      trace.length ≤ freshQueryBound * pairs.length ∧ trace.countP (fun qr => isCut qr.1) ≤ pairs.length := by
  induction pairs generalizing store prior with
  | nil => exact ⟨⟨store, fun _ => none⟩, [], Executes.returned _ _, hstore, Extends.refl store,
      by simp, by simp, by simp, by simp⟩
  | cons pair rest ih =>
    obtain ⟨first, firstTrace, hfirst, hFirstStore, hFirstExt, hFirstRow, hFirstRecord, hFirstQ, hFirstC⟩ :=
      one_trim_executes view ensure baseline oracle isCut freshQueryBound hEnsure agent parent whole target store hstore hwhole
        hlow hnonneg pair prior
    obtain ⟨tail, tailTrace, htail, hTailStore, hTailExt, hTailRows, hTailRecords, hTailQ, hTailC⟩ :=
      ih first.store hFirstStore (hwhole.mono view hFirstExt parent whole) (prior ++ firstTrace)
    let result : TrimRows GlobalParent Payload Agent Parent n := ⟨tail.store, Function.update tail.rows pair first.endpoint⟩
    have htail' := htail.bind (fun tail => Program.returned
      (⟨tail.store, Function.update tail.rows pair first.endpoint⟩ : TrimRows GlobalParent Payload Agent Parent n))
      (Executes.returned result ((prior ++ firstTrace) ++ tailTrace))
    rw [List.append_nil] at htail'
    refine ⟨result, firstTrace ++ tailTrace, hfirst.bind _ htail', hTailStore, hFirstExt.trans hTailExt, ?_, ?_, ?_, ?_⟩
    · intro other hother
      by_cases heq : other = pair
      · subst other
        simpa only [result, Function.update_self] using hFirstRow
      · simpa only [result, Function.update_of_ne heq] using hTailRows other ((List.mem_cons.mp hother).resolve_left heq)
    · intro other hother
      by_cases heq : other = pair
      · subst other
        simpa only [result, Function.update_self] using hFirstRecord.mono view hTailExt (parent pair.2) first.endpoint
      · simpa only [result, Function.update_of_ne heq] using hTailRecords other ((List.mem_cons.mp hother).resolve_left heq)
    · rw [List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rw [List.countP_append, List.length_cons]
      omega

theorem trim_table_executes (view : Payload → Record n)
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Query ℝ (Suffix.Lookup.Result Payload))
    (baseline : Fin n → Lex (ℝ × ℚ)) (oracle : AdaptiveOracle.Policy Query ℝ)
    (isCut : Query → Bool) (freshQueryBound : ℕ)
    (hEnsure : RecordsTargets view ensure baseline oracle isCut freshQueryBound)
    (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ)) (store : Store GlobalParent Payload)
    (hstore : WellFormed view baseline store) (hwhole : Records view store parent whole)
    (hlow : ∀ i, baseline (agent i) ≤ target i) (hnonneg : ∀ i, 0 ≤ (ofLex (target i)).1)
    (prior : OracleProtocol.History Query ℝ) :
    ∃ newStore table trace, Executes oracle (trimTableProgram view ensure agent parent whole target store) prior (newStore, some table) trace ∧
      WellFormed view baseline newStore ∧ Extends store newStore ∧
      (∀ i p r, table.endpoint i p = some r → Stored view newStore (parent p) r) ∧
      trace.length ≤ freshQueryBound * (Fintype.card Agent * Fintype.card Parent) ∧
      trace.countP (fun qr => isCut qr.1) ≤ Fintype.card Agent * Fintype.card Parent := by
  classical
  obtain ⟨out, trace, hexec, hout, hext, hrows, hrecords, hQ, hC⟩ := trim_list_executes view ensure baseline oracle isCut
    freshQueryBound hEnsure agent parent whole target hlow hnonneg Finset.univ.toList store hstore hwhole prior
  have hall : ∀ pair, RecordRowSpec agent whole target pair (out.rows pair) := fun pair => hrows pair (by simp)
  let table := tableFromRows agent whole target out.rows hall
  have hreturn : Executes oracle (if h : ∀ pair, RecordRowSpec agent whole target pair (out.rows pair) then
      Program.returned (out.store, some (tableFromRows agent whole target out.rows h)) else .returned (out.store, none))
      (prior ++ trace) (out.store, some table) [] := by
    rw [dite_eq_left hall]
    exact Executes.returned _ _
  have hjoined := hexec.bind (fun out => if h : ∀ pair, RecordRowSpec agent whole target pair (out.rows pair) then
    Program.returned (out.store, some (tableFromRows agent whole target out.rows h)) else .returned (out.store, none)) hreturn
  rw [List.append_nil] at hjoined
  refine ⟨out.store, table, trace, ?_, hout, hext, ?_, ?_, ?_⟩
  · simpa only [trimTableProgram, ite_eq_left hnonneg] using hjoined
  · intro i p r hr
    have h := hrecords (i, p) (by simp)
    change out.rows (i, p) = some r at hr
    rw [hr] at h
    exact h
  · simpa only [Finset.length_toList, Finset.card_univ, Fintype.card_prod] using hQ
  · simpa only [Finset.length_toList, Finset.card_univ, Fintype.card_prod] using hC

end EnvyFreeResearch.Full.Chores.SubCorePhysical
