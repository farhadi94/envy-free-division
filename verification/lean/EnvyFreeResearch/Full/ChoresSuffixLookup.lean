import EnvyFreeResearch.Full.ChoresSuffixClipped

/-! Finite formal-target lookup retaining auxiliary physical record data.
The scan reads only the projected formal rows; its returned brackets retain
the complete original records, including unclipped values. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix.Lookup
open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped Classical

variable {n : ℕ} {R : Type*}

inductive Location (R : Type*)
  | reused (record : R)
  | bracket (pre : List R) (left right : R) (post : List R)
  | failed

def Location.prepend (r : R) : Location R → Location R
  | .reused s => .reused s
  | .bracket pre left right post => .bracket (r::pre) left right post
  | .failed => .failed

def locate (view : R → Record n) (i : Fin n) (target : ℝ × ℚ) : List R → Location R
  | [] => .failed
  | left::rest =>
    if (view left).formal i = target then .reused left else
      match rest with
      | [] => .failed
      | right::post =>
        if recordLT ((view left).formal i) target ∧ recordLT target ((view right).formal i) then
          .bracket [] left right post
        else (locate view i target rest).prepend left

def Location.Valid (view : R → Record n) (i : Fin n) (target : ℝ × ℚ) (records : List R) :
    Location R → Prop
  | .reused r => r ∈ records ∧ (view r).formal i = target
  | .bracket pre left right post => records = pre ++ left::right::post ∧
      recordLT ((view left).formal i) target ∧ recordLT target ((view right).formal i)
  | .failed => True

theorem locate_valid (view : R → Record n) (i : Fin n) (target : ℝ × ℚ) (records : List R) :
    Location.Valid view i target records (locate view i target records) := by
  induction records with
  | nil => trivial
  | cons left rest ih =>
    rw [locate.eq_def]
    dsimp only
    split_ifs with heq
    · exact ⟨List.mem_cons_self,heq⟩
    · cases rest with
      | nil => trivial
      | cons right post =>
        dsimp only
        split_ifs with hgap
        · exact ⟨rfl,hgap⟩
        · cases hresult : locate view i target (right::post) with
          | failed => trivial
          | reused r =>
            rw [hresult] at ih
            exact ⟨List.mem_cons_of_mem _ ih.1,ih.2⟩
          | bracket pre l r tail =>
            rw [hresult] at ih
            exact ⟨by simpa only [List.cons_append] using congrArg (List.cons left) ih.1,ih.2⟩

theorem Location.prepend_ne_failed (r : R) (l : Location R) (h : l ≠ .failed) :
    l.prepend r ≠ .failed := by cases l <;> simp_all [Location.prepend]

theorem locate_success (view : R → Record n) (i : Fin n) (target : ℝ × ℚ) (first : R) (rest : List R)
    (hlower : recordLT ((view first).formal i) target ∨ (view first).formal i = target)
    (hupper : ∃ last ∈ first::rest, recordLT target ((view last).formal i) ∨ (view last).formal i = target) :
    locate view i target (first::rest) ≠ .failed := by
  induction rest generalizing first with
  | nil =>
    obtain ⟨last,hlast,hu⟩ := hupper
    have hlast' : last = first := by simpa using hlast
    subst last
    have heq : (view first).formal i = target := by
      rcases hlower with hl | heq
      · rcases hu with hu | heq
        · exact (recordLT_irrefl _ (recordLT_trans hl hu)).elim
        · exact heq
      · exact heq
    simp [locate,heq]
  | cons second tail ih =>
    by_cases heq : (view first).formal i = target
    · simp [locate,heq]
    · have hlt : recordLT ((view first).formal i) target := hlower.resolve_right heq
      have hu : ∃ last ∈ second::tail,
          recordLT target ((view last).formal i) ∨ (view last).formal i = target := by
        obtain ⟨last,hlast,hvalue⟩ := hupper
        rcases List.mem_cons.mp hlast with rfl | hlast
        · rcases hvalue with hu | hu
          · exact (recordLT_irrefl _ (recordLT_trans hlt hu)).elim
          · exact (heq hu).elim
        · exact ⟨last,hlast,hvalue⟩
      by_cases hgap : recordLT ((view first).formal i) target ∧ recordLT target ((view second).formal i)
      · simp only [locate,ite_eq_right heq,ite_eq_left hgap]
        intro h
        cases h
      · have hnext : recordLT ((view second).formal i) target ∨ (view second).formal i = target := by
          rcases record_trichotomy ((view second).formal i) target with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hgap ⟨hlt,h⟩).elim
        have hrec := ih second hnext hu
        simpa only [locate,ite_eq_right heq,ite_eq_right hgap] using
          Location.prepend_ne_failed first (locate view i target (second::tail)) hrec

structure Result (R : Type*) where
  records : List R
  selected : R

def ensureProgram (view : R → Record n)
    (insert : R → R → Fin n → ℝ × ℚ → Program (Query (Fin n)) ℝ R)
    (records : List R) (i : Fin n) (target : ℝ × ℚ) : Program (Query (Fin n)) ℝ (Result R) :=
  match locate view i target records with
  | .failed => .failed
  | .reused r => .returned ⟨records,r⟩
  | .bracket pre left right post => (insert left right i target).bind
      (fun fresh => .returned ⟨pre ++ left::fresh::right::post,fresh⟩)

theorem ensure_correct (view : R → Record n)
    (insert : R → R → Fin n → ℝ × ℚ → Program (Query (Fin n)) ℝ R)
    (Good : R → Prop) (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hinsert : ∀ left right i target, Good left → Good right → Before (view left) (view right) →
      0 ≤ (view left).point → (view right).point ≤ 1 →
      recordLT ((view left).formal i) target → recordLT target ((view right).formal i) →
      ∀ prior, ∃ fresh : R, ∃ trace : History (Query (Fin n)) ℝ,
        Executes oracle (insert left right i target) prior fresh trace ∧ trace.length ≤ n ∧
        trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧ Good fresh ∧
        Before (view left) (view fresh) ∧ Before (view fresh) (view right) ∧ (view fresh).formal i = target)
    (first : R) (rest : List R) (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise (fun r s => Before (view r) (view s)) (first::rest))
    (hsound : ∀ r ∈ first::rest, Good r) (hbound : ∀ r ∈ first::rest, (view r).point ∈ Icc (0 : ℝ) 1)
    (hlower : recordLT ((view first).formal i) target ∨ (view first).formal i = target)
    (hupper : ∃ last ∈ first::rest, recordLT target ((view last).formal i) ∨ (view last).formal i = target)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : Result R, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (ensureProgram view insert (first::rest) i target) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise (fun r s => Before (view r) (view s)) result.records ∧
      (∀ r ∈ result.records, Good r ∧ (view r).point ∈ Icc (0 : ℝ) 1) ∧
      (first::rest).Sublist result.records ∧ result.records.length ≤ (first::rest).length+1 ∧
      result.records.head? = (first::rest).head? ∧ result.records.getLast? = (first::rest).getLast? ∧
      result.selected ∈ result.records ∧ (view result.selected).formal i = target := by
  have hsuccess := locate_success view i target first rest hlower hupper
  have hvalid := locate_valid view i target (first::rest)
  cases hloc : locate view i target (first::rest) with
  | failed => exact (hsuccess hloc).elim
  | reused r =>
    rw [hloc] at hvalid
    let result : Result R := ⟨first::rest,r⟩
    refine ⟨result,[],?_,Nat.zero_le _,by simp,horder,
      fun s hs => ⟨hsound s hs,hbound s hs⟩,List.Sublist.refl _,Nat.le_add_right _ _,
      rfl,rfl,hvalid.1,hvalid.2⟩
    simpa only [ensureProgram,hloc] using (Executes.returned (oracle := oracle) result prior)
  | bracket pre left right post =>
    rw [hloc] at hvalid
    obtain ⟨hdecomp,hlt,hrt⟩ := hvalid
    have hleftmem : left ∈ first::rest := by rw [hdecomp]; simp
    have hrightmem : right ∈ first::rest := by rw [hdecomp]; simp
    have horder' : List.Pairwise (fun r s => Before (view r) (view s)) (pre ++ left::right::post) := hdecomp ▸ horder
    have hbefore : Before (view left) (view right) :=
      (List.pairwise_cons.mp (List.pairwise_append.mp horder').2.1).1 right List.mem_cons_self
    obtain ⟨fresh,trace,hexec,hlen,hcuts,hfresh,hlfresh,hfreshr,hcopy⟩ :=
      hinsert left right i target (hsound _ hleftmem) (hsound _ hrightmem) hbefore
        (hbound _ hleftmem).1 (hbound _ hrightmem).2 hlt hrt prior
    let result : Result R := ⟨pre ++ left::fresh::right::post,fresh⟩
    refine ⟨result,trace,?_,hlen,hcuts,
      pairwise_insert_between (fun r s => Before (view r) (view s)) (fun h h' => h.trans h')
        pre post left right fresh horder' hlfresh hfreshr,?_,?_,?_,?_,?_,?_,hcopy⟩
    · simpa only [ensureProgram,hloc,List.append_nil] using hexec.bind
        (fun fresh => Program.returned (⟨pre ++ left::fresh::right::post,fresh⟩ : Result R))
        (Executes.returned result (prior++trace))
    · intro r hr
      rcases inserted_members pre post left right fresh r hr with rfl | hr
      · exact ⟨hfresh,(hbound _ hleftmem).1.trans hlfresh.1,hfreshr.1.trans (hbound _ hrightmem).2⟩
      · exact ⟨hsound r (hdecomp ▸ hr),hbound r (hdecomp ▸ hr)⟩
    · rw [hdecomp]
      exact old_records_sublist pre post left right fresh
    · change (pre ++ left::fresh::right::post).length ≤ (first::rest).length+1
      rw [hdecomp]
      simp only [List.length_append,List.length_cons]
      omega
    · change (pre ++ left::fresh::right::post).head? = (first::rest).head?
      rw [hdecomp]
      exact insert_head_preserved pre post left right fresh
    · change (pre ++ left::fresh::right::post).getLast? = (first::rest).getLast?
      rw [hdecomp]
      exact insert_last_preserved pre post left right fresh
    · simp [result]

end EnvyFreeResearch.Full.Chores.Suffix.Lookup
