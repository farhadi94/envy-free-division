import EnvyFreeResearch.Full.ChoresProgram
import EnvyFreeResearch.Full.ChoresHungryTable

/-!
# One shared physical record store for all Core states and failed candidates

Every parent has an immutable empty and whole record. The single-parent
protocol updates exactly one list and is embedded into the verified query
program compiler, with the full enclosing history supplied to every oracle
call. Old records on every parent remain available without modification.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Persistent

open Set OracleProtocol IntervalOracle QueryProgram
open scoped BigOperators

abbrev Store (n : ℕ) := Fin n → List (Record n)

structure Frame (n : ℕ) where
  base : Fin n → ℝ
  empty : Fin n → Record n
  whole : Fin n → Record n

def ValidStore {n : ℕ} (P : Profile (Fin n)) (frame : Frame n) (store : Store n) : Prop :=
  ∀ p, List.Pairwise Before (store p) ∧
    (∀ r ∈ store p, Sound P (frame.base p) r ∧ r.point ∈ Icc (0 : ℝ) 1) ∧
    (store p).head? = some (frame.empty p) ∧ (store p).getLast? = some (frame.whole p)

structure StoreResult (n : ℕ) where
  store : Store n
  selected : Record n

/-- This is the physical global insertion operation used by every table trial.
It inspects only the given cached records, chosen parent and formal target. -/
def ensureGlobalProgram {n : ℕ} (store : Store n) (i p : Fin n) (target : ℝ × ℚ) :
    Program (Query (Fin n)) ℝ (StoreResult n) :=
  (ofProtocol (ensureProtocol (store p) i target) n []).bind (fun result =>
    .returned ⟨Function.update store p result.records, result.selected⟩)

lemma store_length_update {n : ℕ} (store : Store n) (p : Fin n) (records : List (Record n))
    (hlen : records.length ≤ (store p).length + 1) :
    (∑ q, (Function.update store p records q).length) ≤ (∑ q, (store q).length) + 1 := by
  classical
  have heq : (fun q => (Function.update store p records q).length) =
      Function.update (fun q => (store q).length) p records.length := by
    funext q
    by_cases hq : q = p <;> simp [hq]
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ p)]
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun q => (store q).length)
    (Finset.mem_univ p)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

/-- The complete global physical operation, including actual policy replies
under an arbitrary nonempty prior history. A single successful insertion adds
at most one formal record to the entire global table. -/
theorem ensure_global_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (i p : Fin n) (target : ℝ × ℚ)
    (hlower : recordLE ((frame.empty p).formal i) target)
    (hupper : recordLE target ((frame.whole p).formal i))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : StoreResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (ensureGlobalProgram store i p target) prior result trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∑ q, (result.store q).length) ≤ (∑ q, (store q).length) + 1 ∧
      result.selected ∈ result.store p ∧ result.selected.formal i = target := by
  classical
  obtain ⟨rest, hlist⟩ := List.head?_eq_some_iff.mp (hvalid p).2.2.1
  have hwhole : frame.whole p ∈ store p := by
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp (hvalid p).2.2.2
    rw [hpre]
    simp
  let shifted := fun h => oracle (prior ++ h)
  have hshifted : AdaptiveOracle.IsLegalPolicy P shifted := fun h => hpolicy (prior ++ h)
  have hl : recordLT ((frame.empty p).formal i) target ∨ (frame.empty p).formal i = target := hlower
  have hu : ∃ last ∈ frame.empty p :: rest,
      recordLT target (last.formal i) ∨ last.formal i = target := by
    refine ⟨frame.whole p, hlist ▸ hwhole, ?_⟩
    rcases hupper with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  obtain ⟨r, hstop, hlen, hcuts, horder, hsound, hsub, hsize, hhead, hlast, hselected, htarget⟩ :=
    ensure_protocol_correct P hmono shifted hshifted (frame.base p) (frame.empty p) rest i target
      (hlist ▸ (hvalid p).1) (fun q hq => ((hvalid p).2.1 q (hlist ▸ hq)).1)
      (fun q hq => ((hvalid p).2.1 q (hlist ▸ hq)).2) hl hu
  have hstop' : (AdaptiveOracle.run (ensureProtocol (store p) i target) shifted () n []).stop = .returned r := by
    simpa only [hlist] using hstop
  let trace := (AdaptiveOracle.run (ensureProtocol (store p) i target) shifted () n []).answered
  let result : StoreResult n := ⟨Function.update store p r.records, r.selected⟩
  have hexec : Executes oracle (ofProtocol (ensureProtocol (store p) i target) n []) prior r trace := by
    simpa only [List.append_nil] using ofProtocol_executes (ensureProtocol (store p) i target)
      oracle prior n [] r hstop'
  have hprogram : Executes oracle (ensureGlobalProgram store i p target) prior result trace := by
    have h := hexec.bind (fun output => Program.returned
      (⟨Function.update store p output.records, output.selected⟩ : StoreResult n))
      (Executes.returned result (prior ++ trace))
    simpa only [ensureGlobalProgram, List.append_nil] using h
  refine ⟨result, trace, hprogram, ?_, ?_, ?_, ?_, ?_, ?_, htarget⟩
  · simpa only [trace, hlist] using hlen
  · simpa only [trace, hlist] using hcuts
  · intro q
    by_cases hq : q = p
    · subst q
      simp only [result, Function.update_self]
      exact ⟨horder, hsound, hhead.trans (by simpa only [← hlist] using (hvalid p).2.2.1),
        hlast.trans (by simpa only [← hlist] using (hvalid p).2.2.2)⟩
    · simpa only [result, Function.update_of_ne hq] using hvalid q
  · intro q
    by_cases hq : q = p
    · subst q
      simpa only [result, Function.update_self, hlist] using hsub
    · simpa only [result, Function.update_of_ne hq] using List.Sublist.refl (store q)
  · exact store_length_update store p r.records (by simpa only [hlist] using hsize)
  · simpa only [result, Function.update_self] using hselected

/-- Initial empty/whole rows remain distinct formal records even on physically
empty parents and for observers assigning zero cost to the whole parent. -/
def initialFrame {n : ℕ} (left right : Fin n → ℝ) (wholeValue : Fin n → Fin n → ℝ) : Frame n where
  base := left
  empty p := ⟨left p, fun _ => (0, 0)⟩
  whole p := ⟨right p, fun i => (wholeValue i p, 1)⟩

def initialStore {n : ℕ} (frame : Frame n) : Store n := fun p => [frame.empty p, frame.whole p]

/-- Cached whole interval values initialize the actual global invariant.
This does not treat obtaining those cached values as a free oracle action. -/
theorem initialStore_valid {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (left right : Fin n → ℝ) (wholeValue : Fin n → Fin n → ℝ)
    (hbound : ∀ p, 0 ≤ left p ∧ left p ≤ right p ∧ right p ≤ 1)
    (hvalue : ∀ i p, wholeValue i p = P.cumulative i (right p) - P.cumulative i (left p)) :
    ValidStore P (initialFrame left right wholeValue) (initialStore (initialFrame left right wholeValue)) := by
  intro p
  have hwhole : ∀ i, 0 ≤ wholeValue i p := by
    intro i
    rw [hvalue]
    exact sub_nonneg.mpr (hmono i (hbound p).2.1)
  refine ⟨?_, ?_, rfl, rfl⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, by simp⟩
    intro r hr
    have hr' : r = (initialFrame left right wholeValue).whole p := by simpa [initialStore] using hr
    subst r
    refine ⟨(hbound p).2.1, ?_⟩
    intro i
    by_cases hzero : wholeValue i p = 0
    · right
      exact ⟨hzero.symm, by norm_num [initialFrame]⟩
    · left
      exact lt_of_le_of_ne (hwhole i) (Ne.symm hzero)
  · intro r hr
    rcases (show r = (initialFrame left right wholeValue).empty p ∨
        r = (initialFrame left right wholeValue).whole p from by simpa [initialStore] using hr) with rfl | rfl
    · exact ⟨fun i => by simp [initialFrame], (hbound p).1, (hbound p).2.1.trans (hbound p).2.2⟩
    · exact ⟨fun i => hvalue i p, (hbound p).1.trans (hbound p).2.1, (hbound p).2.2⟩

end EnvyFreeResearch.Full.Chores.Persistent
