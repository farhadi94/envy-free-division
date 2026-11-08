import EnvyFreeResearch.Full.ChoresGlobalRecords
import EnvyFreeResearch.Full.ChoresMemoTrace

/-!
# Formal-record Core candidates with genuine physical trim programs

Candidate decisions use only cached rows. A failed whole-parent comparison
invokes the proved shared-store physical operation; each failed EF candidate
still keeps all records obtained during its exploration. Success of the full
nonhungry table requires the global finite-realization replay proved separately.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent

lemma recordLE_iff_toLex_le (a b : ℝ × ℚ) : recordLE a b ↔ toLex a ≤ toLex b := by
  rw [le_iff_lt_or_eq, Prod.Lex.toLex_lt_toLex]
  simp only [recordLE, recordLT, Equiv.apply_eq_iff_eq]

lemma recordLT_iff_toLex_lt (a b : ℝ × ℚ) : recordLT a b ↔ toLex a < toLex b :=
  Prod.Lex.toLex_lt_toLex.symm

structure State (n k : ℕ) where
  endpoint : Fin k → Record n
  matching : Equiv.Perm (Fin k)

def References {n k : ℕ} (store : Store n) (K : Core.Memo.Key n k) (s : State n k) : Prop :=
  ∀ p, s.endpoint p ∈ store (K.2 p)

def EnvyFree {n k : ℕ} (K : Core.Memo.Key n k) (s : State n k) : Prop :=
  ∀ i p, recordLE ((s.endpoint (s.matching i)).formal (K.1 i)) ((s.endpoint p).formal (K.1 i))

def extendState {n k : ℕ} (i p : Fin (k + 1)) (s : State n k) (r : Record n) : State n (k + 1) :=
  ⟨p.insertNth r s.endpoint, Core.extendMatching i p s.matching⟩

def checked {n k : ℕ} (K : Core.Memo.Key n k) (s : State n k) : Option (State n k) := by
  classical
  exact if EnvyFree K s then some s else none

lemma checked_sound {n k : ℕ} (K : Core.Memo.Key n k) (s out : State n k)
    (h : checked K s = some out) : out = s ∧ EnvyFree K out := by
  classical
  unfold checked at h
  split_ifs at h with hEF
  cases Option.some.inj h
  exact ⟨rfl, hEF⟩

def target {n k : ℕ} (frame : Frame n) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k) : ℝ × ℚ := by
  classical
  exact if h : (Finset.univ : Finset (Fin k)).Nonempty then
    ofLex (Finset.univ.inf' h (fun q => toLex ((s.endpoint q).formal (K.1 i))))
  else (frame.whole (K.2 p)).formal (K.1 i)

lemma whole_mem {n : ℕ} (P : Profile (Fin n)) (frame : Frame n) (store : Store n)
    (hvalid : ValidStore P frame store) (p : Fin n) : frame.whole p ∈ store p := by
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp (hvalid p).2.2.2
  rw [hpre]
  simp

lemma record_nonnegative {n : ℕ} (P : Profile (Fin n)) (frame : Frame n) (store : Store n)
    (hvalid : ValidStore P frame store) (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (p i : Fin n) (r : Record n) (hr : r ∈ store p) : recordLE (0, 0) (r.formal i) := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp (hvalid p).2.2.1
  rw [hrest] at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Or.inr (hzero p i).symm
  · have hbefore := (List.pairwise_cons.mp (hrest ▸ (hvalid p).1)).1 r hr
    exact Or.inl (by simpa only [hzero p i] using hbefore.2 i)

/-- Every formal trim target is nonnegative because it is an actual minimum
of cached physical-prefix records with immutable zero empty labels. -/
lemma target_nonnegative {n k : ℕ} (P : Profile (Fin n))
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (s : State n k)
    (href : References store (Core.Memo.remove K i p) s) : recordLE (0, 0) (target frame K i p s) := by
  classical
  unfold target
  split_ifs with h
  · apply (recordLE_iff_toLex_le _ _).mpr
    change toLex (0, 0) ≤ Finset.univ.inf' h (fun q => toLex ((s.endpoint q).formal (K.1 i)))
    apply Finset.le_inf'
    intro q _
    exact (recordLE_iff_toLex_le _ _).mp (record_nonnegative P frame store hvalid hzero
      ((Core.Memo.remove K i p).2 q) (K.1 i) (s.endpoint q) (href q))
  · exact record_nonnegative P frame store hvalid hzero (K.2 p) (K.1 i)
      (frame.whole (K.2 p)) (whole_mem P frame store hvalid _)

lemma target_lt_whole {n k : ℕ} (frame : Frame n) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k)
    (h : ¬recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s)) :
    recordLT (target frame K i p s) ((frame.whole (K.2 p)).formal (K.1 i)) := by
  apply (recordLT_iff_toLex_lt _ _).mpr
  exact lt_of_not_ge (fun hh => h ((recordLE_iff_toLex_le _ _).mpr hh))

lemma extend_references {n k : ℕ} (oldStore newStore : Store n)
    (hkeep : ∀ q, (oldStore q).Sublist (newStore q))
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (s : State n k) (r : Record n)
    (hold : References oldStore (Core.Memo.remove K i p) s) (hr : r ∈ newStore (K.2 p)) :
    References newStore K (extendState i p s r) := by
  intro q
  obtain hq | ⟨j, hj⟩ := Fin.eq_self_or_eq_succAbove p q
  · subst q
    simpa only [extendState, Fin.insertNth_apply_same] using hr
  · subst q
    have h := (hkeep ((Core.Memo.remove K i p).2 j)).subset (hold j)
    simpa only [extendState, Fin.insertNth_apply_succAbove, Core.Memo.remove,
      RelEmbedding.coe_trans, Fin.coe_succAboveOrderEmb, Function.comp_apply] using h

structure TrialResult (n k : ℕ) where
  store : Store n
  output : Option (State n k)

/-- One actual Core trial. The store update survives an unsuccessful EF test. -/
def trialProgram {n k : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (old : Option (State n k)) :
    Program (Query (Fin n)) ℝ (TrialResult n (k + 1)) := by
  classical
  exact match old with
  | none => .returned ⟨store, none⟩
  | some s =>
    let t := target frame K i p s
    if recordLE ((frame.whole (K.2 p)).formal (K.1 i)) t then
      .returned ⟨store, checked K (extendState i p s (frame.whole (K.2 p)))⟩
    else (ensureGlobalProgram store (K.1 i) (K.2 p) t).bind (fun r =>
      .returned ⟨r.store, checked K (extendState i p s r.selected)⟩)

/-- Every trial physically terminates, preserves the entire global store and
validates every returned candidate. No earlier successful EF cache is assumed
for query legality: membership of its selected immutable records suffices. -/
theorem trial_program_correct {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (old : Option (State n k))
    (hold : ∀ s, old = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : TrialResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (trialProgram frame store K i p old) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  classical
  cases old with
  | none =>
    refine ⟨⟨store, none⟩, [], ?_, by simp, by simp, hvalid, fun _ => List.Sublist.refl _, ?_⟩
    · exact Executes.returned _ _
    · intro s hs
      cases hs
  | some s =>
    have href := hold s rfl
    let t := target frame K i p s
    by_cases hwhole : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) t
    · let candidate := extendState i p s (frame.whole (K.2 p))
      let result : TrialResult n (k + 1) := ⟨store, checked K candidate⟩
      have hprogram : trialProgram frame store K i p (some s) = .returned result := by
        simp only [trialProgram, t, ite_eq_left hwhole]
        rfl
      refine ⟨result, [], ?_, by simp, by simp, hvalid, fun _ => List.Sublist.refl _, ?_⟩
      · rw [hprogram]
        exact Executes.returned _ _
      · intro out hout
        obtain ⟨rfl, hEF⟩ := checked_sound K candidate out hout
        exact ⟨extend_references store store (fun _ => List.Sublist.refl _) K i p s _ href
          (whole_mem P frame store hvalid _), hEF⟩
    · have hlow : recordLE ((frame.empty (K.2 p)).formal (K.1 i)) t := by
        rw [hzero]
        exact target_nonnegative P frame store hvalid hzero K i p s href
      have hhigh : recordLE t ((frame.whole (K.2 p)).formal (K.1 i)) :=
        Or.inl (target_lt_whole frame K i p s hwhole)
      obtain ⟨r, trace, hexec, hlen, hcuts, hstore, hkeep, _, hselected, _⟩ :=
        ensure_global_program_correct P hmono oracle hpolicy frame store hvalid (K.1 i) (K.2 p) t hlow hhigh prior
      let candidate := extendState i p s r.selected
      let result : TrialResult n (k + 1) := ⟨r.store, checked K candidate⟩
      have hprogram : trialProgram frame store K i p (some s) =
          (ensureGlobalProgram store (K.1 i) (K.2 p) t).bind (fun out =>
            .returned ⟨out.store, checked K (extendState i p s out.selected)⟩) := by
        simp only [trialProgram, t, ite_eq_right hwhole]
      refine ⟨result, trace, ?_, hlen, hcuts, hstore, hkeep, ?_⟩
      · rw [hprogram]
        simpa only [List.append_nil] using hexec.bind (fun out => Program.returned
          (⟨out.store, checked K (extendState i p s out.selected)⟩ : TrialResult n (k + 1)))
          (Executes.returned result (prior ++ trace))
      · intro out hout
        obtain ⟨rfl, hEF⟩ := checked_sound K candidate out hout
        exact ⟨extend_references store r.store hkeep K i p s _ href hselected, hEF⟩

end EnvyFreeResearch.Full.Chores.PhysicalCore
