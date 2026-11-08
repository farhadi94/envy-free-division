import EnvyFreeResearch.Full.ChoresPersistent

/-!
# Finite physical-record lookup and adjacent-bracket search

The search reads only the immutable recorded rows. It either reuses an exact
formal target or returns the actual adjacent neighbors enclosing it. Targets
between the first and some later recorded value cannot fail. This includes
formal targets whose primary value is zero or lies on a physical plateau.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Persistent

open Set OracleProtocol IntervalOracle

inductive Location (n : ℕ)
  | reused (record : Record n)
  | bracket (pre : List (Record n)) (left right : Record n) (post : List (Record n))
  | failed

def Location.prepend {n : ℕ} (r : Record n) : Location n → Location n
  | .reused s => .reused s
  | .bracket pre left right post => .bracket (r :: pre) left right post
  | .failed => .failed

/-- Fixed left-to-right scan; no value is read from an unrecorded endpoint. -/
def locate {n : ℕ} (i : Fin n) (target : ℝ × ℚ) : List (Record n) → Location n
  | [] => .failed
  | left :: rest => by
    classical
    exact if left.formal i = target then .reused left else
      match rest with
      | [] => .failed
      | right :: post =>
        if recordLT (left.formal i) target ∧ recordLT target (right.formal i) then
          .bracket [] left right post
        else (locate i target rest).prepend left

def Location.Valid {n : ℕ} (i : Fin n) (target : ℝ × ℚ) (records : List (Record n)) :
    Location n → Prop
  | .reused r => r ∈ records ∧ r.formal i = target
  | .bracket pre left right post => records = pre ++ left :: right :: post ∧
      recordLT (left.formal i) target ∧ recordLT target (right.formal i)
  | .failed => True

lemma locate_valid {n : ℕ} (i : Fin n) (target : ℝ × ℚ) (records : List (Record n)) :
    Location.Valid i target records (locate i target records) := by
  classical
  induction records with
  | nil => trivial
  | cons left rest ih =>
    rw [locate.eq_def]
    dsimp only
    split_ifs with heq
    · exact ⟨List.mem_cons_self, heq⟩
    · cases rest with
      | nil => trivial
      | cons right post =>
        dsimp only
        split_ifs with hgap
        · exact ⟨rfl, hgap⟩
        · cases hresult : locate i target (right :: post) with
          | failed => trivial
          | reused r =>
            rw [hresult] at ih
            exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩
          | bracket pre l r tail =>
            rw [hresult] at ih
            exact ⟨by simpa only [List.cons_append] using congrArg (List.cons left) ih.1, ih.2⟩

lemma recordLT_irrefl (x : ℝ × ℚ) : ¬recordLT x x := by simp [recordLT]

lemma Location.prepend_ne_failed {n : ℕ} (r : Record n) (l : Location n)
    (h : l ≠ .failed) : l.prepend r ≠ .failed := by cases l <;> simp_all [Location.prepend]

/-- A lower bound at the first record and any upper recorded bound ensure
that the finite scan finds either an exact record or a strict adjacent bracket. -/
theorem locate_success {n : ℕ} (i : Fin n) (target : ℝ × ℚ)
    (first : Record n) (rest : List (Record n))
    (hlower : recordLT (first.formal i) target ∨ first.formal i = target)
    (hupper : ∃ last ∈ first :: rest, recordLT target (last.formal i) ∨ last.formal i = target) :
    locate i target (first :: rest) ≠ .failed := by
  classical
  induction rest generalizing first with
  | nil =>
    obtain ⟨last, hlast, hu⟩ := hupper
    have hlast' : last = first := by simpa using hlast
    subst last
    have heq : first.formal i = target := by
      rcases hlower with hl | heq
      · rcases hu with hu | heq
        · exact (recordLT_irrefl _ (recordLT_trans hl hu)).elim
        · exact heq
      · exact heq
    simp [locate, heq]
  | cons second tail ih =>
    by_cases heq : first.formal i = target
    · simp [locate, heq]
    · have hlt : recordLT (first.formal i) target := hlower.resolve_right heq
      have hu : ∃ last ∈ second :: tail,
          recordLT target (last.formal i) ∨ last.formal i = target := by
        obtain ⟨last, hlast, hlastvalue⟩ := hupper
        rcases List.mem_cons.mp hlast with rfl | hlast
        · rcases hlastvalue with hu | hu
          · exact (recordLT_irrefl _ (recordLT_trans hlt hu)).elim
          · exact (heq hu).elim
        · exact ⟨last, hlast, hlastvalue⟩
      by_cases hgap : recordLT (first.formal i) target ∧ recordLT target (second.formal i)
      · simp only [locate, ite_eq_right heq, ite_eq_left hgap]
        intro h
        cases h
      · have hnext : recordLT (second.formal i) target ∨ second.formal i = target := by
          rcases record_trichotomy (second.formal i) target with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hgap ⟨hlt, h⟩).elim
        have hrec := ih second hnext hu
        simpa only [locate, ite_eq_right heq, ite_eq_right hgap] using
          Location.prepend_ne_failed first (locate i target (second :: tail)) hrec

structure EnsureResult (n : ℕ) where
  records : List (Record n)
  selected : Record n

/-- The physical single-parent driver is a concrete next-action protocol.
An existing formal target incurs no query; a new target inserts one record. -/
def ensureProtocol {n : ℕ} (records : List (Record n)) (i : Fin n) (target : ℝ × ℚ) :
    Protocol Unit (Query (Fin n)) ℝ (EnsureResult n) :=
  match locate i target records with
  | .failed => fun _ _ => .diverge
  | .reused r => fun _ _ => .returned ⟨records, r⟩
  | .bracket pre left right post => mapProtocol
      (fun fresh => ⟨pre ++ left :: fresh :: right :: post, fresh⟩)
      (insertionProtocol left right i target)

lemma insert_head_preserved {α : Type*} (pre post : List α) (left right fresh : α) :
    (pre ++ left :: fresh :: right :: post).head? = (pre ++ left :: right :: post).head? := by
  cases pre <;> rfl

lemma insert_last_preserved {α : Type*} (pre post : List α) (left right fresh : α) :
    (pre ++ left :: fresh :: right :: post).getLast? = (pre ++ left :: right :: post).getLast? := by
  simp only [List.getLast?_append, List.getLast?_cons_cons]

/-- A complete single-parent persistent lookup/insert operation: all original
costs, bounds, order and previous rows survive, and the selected record copies
the exact formal target. The ordinary-query ledger is proved from the run. -/
theorem ensure_protocol_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (base : ℝ) (first : Record n) (rest : List (Record n)) (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise Before (first :: rest))
    (hsound : ∀ r ∈ first :: rest, Sound P base r)
    (hbound : ∀ r ∈ first :: rest, r.point ∈ Icc (0 : ℝ) 1)
    (hlower : recordLT (first.formal i) target ∨ first.formal i = target)
    (hupper : ∃ last ∈ first :: rest, recordLT target (last.formal i) ∨ last.formal i = target) :
    ∃ result : EnsureResult n,
      (AdaptiveOracle.run (ensureProtocol (first :: rest) i target) oracle () n []).stop = .returned result ∧
      (AdaptiveOracle.run (ensureProtocol (first :: rest) i target) oracle () n []).answered.length ≤ n ∧
      (AdaptiveOracle.run (ensureProtocol (first :: rest) i target) oracle () n []).answered.countP
        (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise Before result.records ∧
      (∀ r ∈ result.records, Sound P base r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
      (first :: rest).Sublist result.records ∧ result.records.length ≤ (first :: rest).length + 1 ∧
      result.records.head? = (first :: rest).head? ∧ result.records.getLast? = (first :: rest).getLast? ∧
      result.selected ∈ result.records ∧ result.selected.formal i = target := by
  classical
  have hsuccess := locate_success i target first rest hlower hupper
  have hvalid := locate_valid i target (first :: rest)
  cases hloc : locate i target (first :: rest) with
  | failed => exact (hsuccess hloc).elim
  | reused r =>
    rw [hloc] at hvalid
    let result : EnsureResult n := ⟨first :: rest, r⟩
    have hrun : AdaptiveOracle.run (ensureProtocol (first :: rest) i target) oracle () n [] =
        ⟨[], .returned result⟩ := by
      apply AdaptiveOracle.run_returned
      simp [ensureProtocol, hloc, result]
    refine ⟨result, ?_, ?_, ?_, horder, fun s hs => ⟨hsound s hs, hbound s hs⟩,
      List.Sublist.refl _, Nat.le_add_right _ _, rfl, rfl, hvalid.1, hvalid.2⟩
    all_goals simp [hrun]
  | bracket pre left right post =>
    rw [hloc] at hvalid
    obtain ⟨hdecomp, hlt, hrt⟩ := hvalid
    have hleftmem : left ∈ first :: rest := by rw [hdecomp]; simp
    have hrightmem : right ∈ first :: rest := by rw [hdecomp]; simp
    have horder' : List.Pairwise Before (pre ++ left :: right :: post) := hdecomp ▸ horder
    have hbefore : Before left right :=
      (List.pairwise_cons.mp (List.pairwise_append.mp horder').2.1).1 right List.mem_cons_self
    obtain ⟨fresh, hstop, hlen, hcuts, hf, hlf, hfr, hcopy⟩ := insertion_protocol_correct
      P hmono oracle hpolicy base left right i target (hsound _ hleftmem) (hsound _ hrightmem)
      hbefore (hbound _ hleftmem).1 (hbound _ hrightmem).2 hlt hrt
    let result : EnsureResult n := ⟨pre ++ left :: fresh :: right :: post, fresh⟩
    have hproto : ensureProtocol (first :: rest) i target = mapProtocol
        (fun fresh => (⟨pre ++ left :: fresh :: right :: post, fresh⟩ : EnsureResult n))
        (insertionProtocol left right i target) := by simp [ensureProtocol, hloc]
    have hrun := run_mapProtocol (fun fresh => (⟨pre ++ left :: fresh :: right :: post, fresh⟩ : EnsureResult n))
      (insertionProtocol left right i target) oracle () n []
    refine ⟨result, ?_, ?_, ?_, pairwise_insert_between Before (fun h h' => h.trans h')
      pre post left right fresh horder' hlf hfr, ?_, ?_, ?_, ?_, ?_, ?_, hcopy⟩
    · rw [hproto, hrun, hstop]
      rfl
    · rw [hproto, hrun]
      exact hlen
    · rw [hproto, hrun]
      exact hcuts
    · intro r hr
      rcases inserted_members pre post left right fresh r hr with rfl | hr
      · exact ⟨hf, (hbound _ hleftmem).1.trans hlf.1, hfr.1.trans (hbound _ hrightmem).2⟩
      · exact ⟨hsound r (hdecomp ▸ hr), hbound r (hdecomp ▸ hr)⟩
    · rw [hdecomp]
      exact old_records_sublist pre post left right fresh
    · change (pre ++ left :: fresh :: right :: post).length ≤ (first :: rest).length + 1
      rw [hdecomp]
      simp only [List.length_append, List.length_cons]
      omega
    · change (pre ++ left :: fresh :: right :: post).head? = (first :: rest).head?
      rw [hdecomp]
      exact insert_head_preserved pre post left right fresh
    · change (pre ++ left :: fresh :: right :: post).getLast? = (first :: rest).getLast?
      rw [hdecomp]
      exact insert_last_preserved pre post left right fresh
    · simp [result]

end EnvyFreeResearch.Full.Chores.Persistent
