import EnvyFreeResearch.Full.ChoresEndpointQueries
import EnvyFreeResearch.Full.ChoresRecordInsertion

/-!
# Permanent physical records and their actual insertion protocol

The strict formal bracket is implemented by reusing a neighboring physical
coordinate when its primary value is the target, and otherwise by the exact
adaptive endpoint-recording protocol. Every old record is kept literally
unchanged when the new record is inserted between its neighbors.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Persistent

open Set OracleProtocol IntervalOracle

/-- Output mapping preserves asks, full-history replies, and termination. -/
def mapProtocol {Tape Query Reply A B : Type*} (f : A → B)
    (next : Protocol Tape Query Reply A) : Protocol Tape Query Reply B :=
  fun tape history => match next tape history with
  | .ask q => .ask q
  | .returned a => .returned (f a)
  | .diverge => .diverge

def mapStop {Query A B : Type*} (f : A → B) : Stop Query A → Stop Query B
  | .returned a => .returned (f a)
  | .diverged => .diverged
  | .illegal q => .illegal q
  | .exhausted q => .exhausted q

lemma run_mapProtocol {Tape Query Reply A B : Type*} (f : A → B)
    (next : Protocol Tape Query Reply A) (oracle : AdaptiveOracle.Policy Query Reply)
    (tape : Tape) (fuel : ℕ) (history : History Query Reply) :
    AdaptiveOracle.run (mapProtocol f next) oracle tape fuel history =
      ⟨(AdaptiveOracle.run next oracle tape fuel history).answered,
        mapStop f (AdaptiveOracle.run next oracle tape fuel history).stop⟩ := by
  induction fuel generalizing history with
  | zero =>
    cases h : next tape history <;> simp [mapProtocol, mapStop, h]
  | succ fuel ih =>
    cases h : next tape history with
    | returned a => simp [mapProtocol, mapStop, h]
    | diverge => simp [mapProtocol, mapStop, h]
    | ask q =>
      cases ho : oracle history q with
      | none => simp [mapProtocol, mapStop, h, ho]
      | some r =>
        have hm : mapProtocol f next tape history = .ask q := by simp [mapProtocol, h]
        rw [AdaptiveOracle.run_succ_some _ _ _ _ _ _ _ hm ho,
          AdaptiveOracle.run_succ_some _ _ _ _ _ _ _ h ho, ih]

structure Record (n : ℕ) where
  point : ℝ
  formal : Fin n → ℝ × ℚ

def Sound {n : ℕ} (P : Profile (Fin n)) (base : ℝ) (r : Record n) : Prop :=
  ∀ i, (r.formal i).1 = P.cumulative i r.point - P.cumulative i base

def Before {n : ℕ} (r s : Record n) : Prop :=
  r.point ≤ s.point ∧ ∀ i, recordLT (r.formal i) (s.formal i)

lemma recordLT_trans {a b c : ℝ × ℚ} (hab : recordLT a b) (hbc : recordLT b c) :
    recordLT a c := by
  rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
  · exact Or.inl (hab.trans hbc)
  · exact Or.inl (by simpa only [← hbc] using hab)
  · exact Or.inl (by simpa only [hab] using hbc)
  · exact Or.inr ⟨hab.trans hbc, hab'.trans hbc'⟩

lemma Before.trans {n : ℕ} {a b c : Record n} (hab : Before a b) (hbc : Before b c) :
    Before a c := ⟨hab.1.trans hbc.1, fun i => recordLT_trans (hab.2 i) (hbc.2 i)⟩

lemma recordLT_primary_le {a b : ℝ × ℚ} (h : recordLT a b) : a.1 ≤ b.1 := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- New labels depend only on immutable neighbors and the newly recorded row. -/
def makeRecord {n : ℕ} (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (point : ℝ) (primary : Fin n → ℝ) : Record n :=
  ⟨point, insertedRecord left.formal right.formal primary i target⟩

def fromEndpoint {n : ℕ} (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (r : EndpointRecord n) : Record n :=
  makeRecord left right i target r.point (fun j => (left.formal j).1 + r.value j)

/-- Both plateau branches return without asking anything. The strict-primary
branch uses only original physical interval queries. -/
def insertionProtocol {n : ℕ} (left right : Record n) (i : Fin n) (target : ℝ × ℚ) :
    Protocol Unit (Query (Fin n)) ℝ (Record n) :=
  if target.1 = (left.formal i).1 then
    fun _ _ => .returned (makeRecord left right i target left.point (fun j => (left.formal j).1))
  else if target.1 = (right.formal i).1 then
    fun _ _ => .returned (makeRecord left right i target right.point (fun j => (right.formal j).1))
  else mapProtocol (fromEndpoint left right i target)
    (endpointProtocol i left.point right.point (target.1 - (left.formal i).1))

lemma makeRecord_spec {n : ℕ} (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (point : ℝ) (primary : Fin n → ℝ) (hbefore : Before left right)
    (hpoint : point ∈ Icc left.point right.point)
    (hbetween : ∀ j, (left.formal j).1 ≤ primary j ∧ primary j ≤ (right.formal j).1)
    (htarget : primary i = target.1)
    (hlt : recordLT (left.formal i) target) (hrt : recordLT target (right.formal i)) :
    Before left (makeRecord left right i target point primary) ∧
    Before (makeRecord left right i target point primary) right ∧
    (makeRecord left right i target point primary).formal i = target := by
  obtain ⟨heq, horder⟩ := insertedRecord_preserves left.formal right.formal primary i target
    hbefore.2 hbetween htarget hlt hrt
  exact ⟨⟨hpoint.1, fun j => (horder j).1⟩, ⟨hpoint.2, fun j => (horder j).2⟩, heq⟩

lemma makeRecord_sound {n : ℕ} (P : Profile (Fin n)) (base : ℝ)
    (left right : Record n) (i : Fin n) (target : ℝ × ℚ) (point : ℝ) (primary : Fin n → ℝ)
    (hprimary : ∀ j, primary j = P.cumulative j point - P.cumulative j base) :
    Sound P base (makeRecord left right i target point primary) := hprimary

/-- Every formal bracket is realized by a terminating profile-independent
protocol. Fresh coordinates use exactly one Cut and at most `n` total queries;
plateau coordinates use zero. All neighbors and labels remain immutable. -/
theorem insertion_protocol_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (base : ℝ) (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (hleft : Sound P base left) (hright : Sound P base right)
    (hbefore : Before left right) (hl0 : 0 ≤ left.point) (hr1 : right.point ≤ 1)
    (hlt : recordLT (left.formal i) target) (hrt : recordLT target (right.formal i)) :
    ∃ r : Record n,
      (AdaptiveOracle.run (insertionProtocol left right i target) oracle () n []).stop = .returned r ∧
      (AdaptiveOracle.run (insertionProtocol left right i target) oracle () n []).answered.length ≤ n ∧
      (AdaptiveOracle.run (insertionProtocol left right i target) oracle () n []).answered.countP
        (fun qr => isCutQuery qr.1) ≤ 1 ∧
      Sound P base r ∧ Before left r ∧ Before r right ∧ r.formal i = target := by
  classical
  have hprim : ∀ j, (left.formal j).1 ≤ (right.formal j).1 :=
    fun j => recordLT_primary_le (hbefore.2 j)
  by_cases hl : target.1 = (left.formal i).1
  · let r := makeRecord left right i target left.point (fun j => (left.formal j).1)
    have hrun : AdaptiveOracle.run (insertionProtocol left right i target) oracle () n [] =
        ⟨[], .returned r⟩ := by
      apply AdaptiveOracle.run_returned
      simp only [insertionProtocol, ite_eq_left hl]
      rfl
    have hs := makeRecord_spec left right i target left.point (fun j => (left.formal j).1)
      hbefore ⟨le_rfl, hbefore.1⟩ (fun j => ⟨le_rfl, hprim j⟩) hl.symm hlt hrt
    refine ⟨r, ?_, ?_, ?_, makeRecord_sound P base left right i target _ _ hleft, hs.1, hs.2⟩
    all_goals simp [hrun]
  · by_cases hr : target.1 = (right.formal i).1
    · let r := makeRecord left right i target right.point (fun j => (right.formal j).1)
      have hrun : AdaptiveOracle.run (insertionProtocol left right i target) oracle () n [] =
          ⟨[], .returned r⟩ := by
        apply AdaptiveOracle.run_returned
        simp only [insertionProtocol, ite_eq_right hl, ite_eq_left hr]
        rfl
      have hs := makeRecord_spec left right i target right.point (fun j => (right.formal j).1)
        hbefore ⟨hbefore.1, le_rfl⟩ (fun j => ⟨hprim j, le_rfl⟩) hr.symm hlt hrt
      refine ⟨r, ?_, ?_, ?_, makeRecord_sound P base left right i target _ _ hright, hs.1, hs.2⟩
      all_goals simp [hrun]
    · have htarget0 : 0 ≤ target.1 - (left.formal i).1 := sub_nonneg.mpr (recordLT_primary_le hlt)
      have htotal : 0 ≤ P.cumulative i right.point - P.cumulative i left.point :=
        sub_nonneg.mpr (hmono i hbefore.1)
      have htarget1 : target.1 - (left.formal i).1 ≤
          P.cumulative i right.point - P.cumulative i left.point := by
        have h := recordLT_primary_le hrt
        rw [hleft i, hright i] at *
        linarith
      have hlegal : Legal P (.cut i left.point right.point (target.1 - (left.formal i).1)) := by
        refine ⟨hl0, hbefore.1, hr1, ?_⟩
        change min 0 _ ≤ _ ∧ _ ≤ max 0 _
        rw [min_eq_left htotal, max_eq_right htotal]
        exact ⟨htarget0, htarget1⟩
      obtain ⟨e, hstop, hlen, hcuts, hepoint, hevalue, hetarget⟩ :=
        endpoint_protocol_correct P oracle hpolicy i left.point right.point _ hlegal
      let r := fromEndpoint left right i target e
      have hrun := run_mapProtocol (fromEndpoint left right i target)
        (endpointProtocol i left.point right.point (target.1 - (left.formal i).1)) oracle () n []
      have hproto : insertionProtocol left right i target = mapProtocol (fromEndpoint left right i target)
          (endpointProtocol i left.point right.point (target.1 - (left.formal i).1)) := by
        simp only [insertionProtocol, ite_eq_right hl, ite_eq_right hr]
      have hprimary : ∀ j, (left.formal j).1 + e.value j =
          P.cumulative j e.point - P.cumulative j base := by
        intro j
        rw [hleft j, hevalue j]
        ring
      have hbetween : ∀ j, (left.formal j).1 ≤ (left.formal j).1 + e.value j ∧
          (left.formal j).1 + e.value j ≤ (right.formal j).1 := by
        intro j
        rw [hprimary j, hleft j, hright j]
        exact ⟨sub_le_sub_right (hmono j hepoint.1) _, sub_le_sub_right (hmono j hepoint.2) _⟩
      have hcopy : (left.formal i).1 + e.value i = target.1 := by rw [hetarget]; ring
      have hs := makeRecord_spec left right i target e.point _ hbefore hepoint hbetween hcopy hlt hrt
      refine ⟨r, ?_, ?_, ?_, makeRecord_sound P base left right i target _ _ hprimary, hs.1, hs.2⟩
      · rw [hproto, hrun, hstop]
        rfl
      · rw [hproto, hrun]
        exact hlen.le
      · rw [hproto, hrun]
        exact hcuts.le

/-- Inserting between adjacent elements preserves a transitive pairwise order.
The proof uses the actual old list, so old data need not be relabeled. -/
lemma pairwise_insert_between {α : Type*} (R : α → α → Prop)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (pre post : List α) (left right fresh : α)
    (hold : List.Pairwise R (pre ++ left :: right :: post))
    (hl : R left fresh) (hr : R fresh right) :
    List.Pairwise R (pre ++ left :: fresh :: right :: post) := by
  obtain ⟨hpre, hrest, hcross⟩ := List.pairwise_append.mp hold
  obtain ⟨hlold, hright⟩ := List.pairwise_cons.mp hrest
  refine List.pairwise_append.mpr ⟨hpre, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hl
      · exact hlold z hz
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hright⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hr
      · exact htrans hr ((List.pairwise_cons.mp hright).1 z hz)
  · intro z hz w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hcross z hz w List.mem_cons_self
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact htrans (hcross z hz left List.mem_cons_self) hl
      · exact hcross z hz w (List.mem_cons_of_mem _ hw)

lemma old_records_sublist {α : Type*} (pre post : List α) (left right fresh : α) :
    (pre ++ left :: right :: post).Sublist (pre ++ left :: fresh :: right :: post) :=
  ((List.Sublist.refl (right :: post)).cons fresh |>.cons_cons left).append_left pre

lemma inserted_members {α : Type*} (pre post : List α) (left right fresh z : α)
    (hz : z ∈ pre ++ left :: fresh :: right :: post) :
    z = fresh ∨ z ∈ pre ++ left :: right :: post := by
  simp only [List.mem_append, List.mem_cons] at *
  tauto

def insertionListProtocol {n : ℕ} (pre post : List (Record n)) (left right : Record n)
    (i : Fin n) (target : ℝ × ℚ) : Protocol Unit (Query (Fin n)) ℝ (List (Record n)) :=
  mapProtocol (fun fresh => pre ++ left :: fresh :: right :: post)
    (insertionProtocol left right i target)

/-- One actual permanent-list transition preserves all recorded values and all
old rows literally, including those belonging to failed exploratory trials.
The result has one more formal record even when its physical coordinate is
reused, and every observer sees strict formal growth along the complete list. -/
theorem insertion_list_protocol_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (base : ℝ) (pre post : List (Record n)) (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (horder : List.Pairwise Before (pre ++ left :: right :: post))
    (hsound : ∀ r ∈ pre ++ left :: right :: post, Sound P base r)
    (hbound : ∀ r ∈ pre ++ left :: right :: post, r.point ∈ Icc (0 : ℝ) 1)
    (hlt : recordLT (left.formal i) target) (hrt : recordLT target (right.formal i)) :
    ∃ fresh : Record n,
      (AdaptiveOracle.run (insertionListProtocol pre post left right i target) oracle () n []).stop =
        .returned (pre ++ left :: fresh :: right :: post) ∧
      (AdaptiveOracle.run (insertionListProtocol pre post left right i target) oracle () n []).answered.length ≤ n ∧
      (AdaptiveOracle.run (insertionListProtocol pre post left right i target) oracle () n []).answered.countP
        (fun qr => isCutQuery qr.1) ≤ 1 ∧
      List.Pairwise Before (pre ++ left :: fresh :: right :: post) ∧
      (∀ r ∈ pre ++ left :: fresh :: right :: post, Sound P base r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
      (pre ++ left :: right :: post).Sublist (pre ++ left :: fresh :: right :: post) ∧
      (pre ++ left :: fresh :: right :: post).length = (pre ++ left :: right :: post).length + 1 ∧
      fresh.formal i = target := by
  have hlmem : left ∈ pre ++ left :: right :: post := by simp
  have hrmem : right ∈ pre ++ left :: right :: post := by simp
  have hbefore : Before left right :=
    (List.pairwise_cons.mp (List.pairwise_append.mp horder).2.1).1 right List.mem_cons_self
  obtain ⟨fresh, hstop, hlen, hcuts, hf, hlf, hfr, hcopy⟩ := insertion_protocol_correct
    P hmono oracle hpolicy base left right i target (hsound _ hlmem) (hsound _ hrmem)
    hbefore (hbound _ hlmem).1 (hbound _ hrmem).2 hlt hrt
  have hrun := run_mapProtocol (fun fresh => pre ++ left :: fresh :: right :: post)
    (insertionProtocol left right i target) oracle () n []
  refine ⟨fresh, ?_, ?_, ?_, pairwise_insert_between Before (fun h h' => h.trans h')
    pre post left right fresh horder hlf hfr, ?_, old_records_sublist pre post left right fresh,
    ?_, hcopy⟩
  · rw [insertionListProtocol, hrun, hstop]
    rfl
  · rw [insertionListProtocol, hrun]
    exact hlen
  · rw [insertionListProtocol, hrun]
    exact hcuts
  · intro r hr
    rcases inserted_members pre post left right fresh r hr with rfl | hr
    · exact ⟨hf, (hbound _ hlmem).1.trans hlf.1, hfr.1.trans (hbound _ hrmem).2⟩
    · exact ⟨hsound r hr, hbound r hr⟩
  · simp only [List.length_append, List.length_cons]
    omega

end EnvyFreeResearch.Full.Chores.Persistent
