import EnvyFreeResearch.Full.ChoresPhysicalCache

/-!
# One hungry realization of the actual final shared physical record store

This adapter indexes the complete retained lists, including failed-candidate
records and duplicate physical coordinates, and applies the proved simultaneous
normalized realization. The immutable whole record is placed at coordinate
one. All original records have one fixed abstract coordinate and every formal
comparison is preserved simultaneously throughout the final store.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Persistent

open Set IntervalOracle

structure StoreRealization {n : ℕ} (frame : Frame n) (store : Store n) where
  costs : Core.HungryCosts n
  coordinate : Fin n → Record n → ℝ
  feasible : ∀ p r, r ∈ store p → coordinate p r ∈ Icc (0 : ℝ) 1
  whole : ∀ p, coordinate p (frame.whole p) = 1
  scale : ℝ
  scale_pos : 0 < scale
  value : ∀ i p r, r ∈ store p → costs.cost i p (coordinate p r) = realizedCost scale (r.formal i)
  compare : ∀ i p r, r ∈ store p → ∀ j q s, s ∈ store q →
    (recordLT (r.formal i) (s.formal j) ↔ costs.cost i p (coordinate p r) < costs.cost j q (coordinate q s)) ∧
    (r.formal i = s.formal j ↔ costs.cost i p (coordinate p r) = costs.cost j q (coordinate q s)) ∧
    (recordLE (r.formal i) (s.formal j) ↔ costs.cost i p (coordinate p r) ≤ costs.cost j q (coordinate q s))

/-- Every valid permanent store with distinct empty/whole formal records has
an actual single hungry realization, with no replay or success premise. -/
theorem exists_store_realization {n : ℕ} (P : Profile (Fin n)) (frame : Frame n) (store : Store n)
    (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hproper : ∀ p, frame.empty p ≠ frame.whole p) : Nonempty (StoreRealization frame store) := by
  classical
  have hne (p : Fin n) : store p ≠ [] := by
    intro h
    have hh := (hvalid p).2.2.1
    simp [h] at hh
  let length := fun p => (store p).length - 1
  have hsize (p : Fin n) : length p + 1 = (store p).length := by
    have h := List.length_pos_iff.mpr (hne p)
    dsimp only [length]
    omega
  have hpositive (p : Fin n) : 0 < length p := by
    cases hlist : store p with
    | nil => exact (hne p hlist).elim
    | cons first rest =>
      cases rest with
      | nil =>
        have hempty : first = frame.empty p := by simpa only [hlist, List.head?_cons, Option.some.injEq] using (hvalid p).2.2.1
        have hwhole : first = frame.whole p := by simpa only [hlist, List.getLast?_singleton, Option.some.injEq] using (hvalid p).2.2.2
        exact (hproper p (hempty.symm.trans hwhole)).elim
      | cons second tail => simp [length, hlist]
  let atRecord := fun p => fun k : Fin (length p + 1) => (store p).get (Fin.cast (hsize p) k)
  have hatzero (p : Fin n) : atRecord p 0 = frame.empty p := by
    have hhead : (store p).head (hne p) = frame.empty p := Option.some.inj
      ((List.head?_eq_some_head (hne p)).symm.trans (hvalid p).2.2.1)
    simpa only [atRecord, List.get_eq_getElem, Fin.val_cast, Fin.val_zero, List.head_eq_getElem] using hhead
  have hatlast (p : Fin n) : atRecord p (Fin.last (length p)) = frame.whole p := by
    have hlast : (store p).getLast (hne p) = frame.whole p := Option.some.inj
      ((List.getLast?_eq_some_getLast (hne p)).symm.trans (hvalid p).2.2.2)
    simpa only [atRecord, List.get_eq_getElem, Fin.val_cast, Fin.val_last, length, List.getLast_eq_getElem] using hlast
  have hex (p : Fin n) (r : Record n) (hr : r ∈ store p) :
      ∃ k : Fin (length p + 1), atRecord p k = r := by
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
    refine ⟨Fin.cast (hsize p).symm k, ?_⟩
    have hcast : Fin.cast (hsize p) (Fin.cast (hsize p).symm k) = k := by apply Fin.ext; rfl
    simpa only [atRecord, hcast] using hk
  let index := fun p r => if r = frame.whole p then Fin.last (length p)
    else if r = frame.empty p then 0
    else if h : r ∈ store p then Classical.choose (hex p r h) else 0
  have hatindex (p : Fin n) (r : Record n) (hr : r ∈ store p) : atRecord p (index p r) = r := by
    dsimp only [index]
    split_ifs with hw he
    · simpa only [hw] using hatlast p
    · simpa only [he] using hatzero p
    · exact Classical.choose_spec (hex p r hr)
  let record := fun i p k => (atRecord p k).formal i
  have hrzero : ∀ i p, record i p 0 = (0, 0) := by
    intro i p
    simp only [record, hatzero, hzero]
  have hrstrict : ∀ i p (j k : Fin (length p + 1)), j < k →
      recordLT (record i p j) (record i p k) := by
    intro i p j k hjk
    exact ((hvalid p).1.rel_get_of_lt (show Fin.cast (hsize p) j < Fin.cast (hsize p) k from hjk)).2 i
  obtain ⟨ε, hε, C, hvalue, hcompare⟩ := simultaneous_hungry_profile n length hpositive record hrzero hrstrict
  let coordinate := fun p r => recordPosition (length p) (index p r)
  refine ⟨⟨C, coordinate, ?_, ?_, ε, hε, ?_, ?_⟩⟩
  · intro p r _
    exact recordPosition_mem (length p) (hpositive p) (index p r)
  · intro p
    simp only [coordinate, index, ite_true, recordPosition_last _ (hpositive _)]
  · intro i p r hr
    have h := hvalue i p (index p r)
    simpa only [record, hatindex p r hr] using h
  · intro i p r hr j q s hs
    have h := hcompare i p (index p r) j q (index q s)
    simpa only [record, hatindex p r hr, hatindex q s hs] using h

/-- Initial formal empty and whole records are distinct even when all their
physical prefix costs and physical endpoints agree. -/
lemma initialFrame_proper {n : ℕ} (hn : 0 < n) (left right : Fin n → ℝ)
    (wholeValue : Fin n → Fin n → ℝ) :
    ∀ p, (initialFrame left right wholeValue).empty p ≠ (initialFrame left right wholeValue).whole p := by
  intro p h
  have hlabel := congrArg (fun r : Record n => (r.formal ⟨0, hn⟩).2) h
  norm_num [initialFrame] at hlabel

end EnvyFreeResearch.Full.Chores.Persistent

namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set Persistent

/-- The same realized coordinate is used for a physical record everywhere it
appears, across all subsets and candidate matchings. -/
def State.realize {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (K : Core.Memo.Key n k) (s : State n k) : Core.State k :=
  ⟨fun p => R.coordinate (K.2 p) (s.endpoint p), s.matching⟩

lemma State.realize_feasible {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (K : Core.Memo.Key n k) (s : State n k)
    (href : References store K s) : Core.Feasible (s.realize R K) :=
  fun p => R.feasible (K.2 p) (s.endpoint p) (href p)

/-- Every EF decision in every realized candidate is exactly the cached formal
decision, including all failed tests, under one shared final-store realization. -/
lemma State.realize_envyFree_iff {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (K : Core.Memo.Key n k) (s : State n k)
    (href : References store K s) :
    Core.EnvyFree (Core.Memo.restrict R.costs K).cost (s.realize R K) ↔ EnvyFree K s := by
  constructor <;> intro h i p
  · exact (R.compare (K.1 i) (K.2 (s.matching i)) (s.endpoint (s.matching i)) (href _)
      (K.1 i) (K.2 p) (s.endpoint p) (href p)).2.2.mpr (h i p)
  · exact (R.compare (K.1 i) (K.2 (s.matching i)) (s.endpoint (s.matching i)) (href _)
      (K.1 i) (K.2 p) (s.endpoint p) (href p)).2.2.mp (h i p)

end EnvyFreeResearch.Full.Chores.PhysicalCore
