import EnvyFreeResearch.Full.ChoresStoreRealization

/-!
# Exact hungry replay of recorded Core candidate geometry

A single realization of the final shared table preserves minima, whole-parent
branches, target roots, and complete EF decisions. These lemmas connect actual
record objects to the existing hungry candidate construction; they do not
assume that the physical dynamic program succeeds.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set Persistent

lemma realize_extend {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k) (r : Record n) :
    (extendState i p s r).realize R K = Core.extendState i p
      (s.realize R (Core.Memo.remove K i p)) (R.coordinate (K.2 p) r) := by
  unfold State.realize extendState Core.extendState
  congr 1
  funext q
  obtain hq | ⟨j, hj⟩ := Fin.eq_self_or_eq_succAbove p q
  · subst q
    simp
  · subst q
    simp [Core.Memo.remove, RelEmbedding.coe_trans]

lemma target_attained {n k : ℕ} (frame : Frame n) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k) (h : (Finset.univ : Finset (Fin k)).Nonempty) :
    ∃ q, target frame K i p s = (s.endpoint q).formal (K.1 i) ∧
      ∀ r, recordLE ((s.endpoint q).formal (K.1 i)) ((s.endpoint r).formal (K.1 i)) := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf' h (fun q => toLex ((s.endpoint q).formal (K.1 i)))
  refine ⟨q, ?_, ?_⟩
  · rw [target, dite_eq_left h, hq, ofLex_toLex]
  · intro r
    apply (recordLE_iff_toLex_le _ _).mpr
    rw [← hq]
    exact Finset.inf'_le _ (Finset.mem_univ r)

/-- Every formal target is the value of an actual old record somewhere in the
same final table, including the singleton whole-parent target. -/
lemma target_existing_record {n k : ℕ} (P : IntervalOracle.Profile (Fin n))
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (s : State n k)
    (href : References store (Core.Memo.remove K i p) s) :
    ∃ q r, r ∈ store q ∧ target frame K i p s = r.formal (K.1 i) := by
  classical
  by_cases h : (Finset.univ : Finset (Fin k)).Nonempty
  · obtain ⟨q, hq, _⟩ := target_attained frame K i p s h
    exact ⟨(Core.Memo.remove K i p).2 q, s.endpoint q, href q, hq⟩
  · exact ⟨K.2 p, frame.whole (K.2 p), whole_mem P frame store hvalid _, by simp [target, h]⟩

/-- Formal and hungry minima are equal under the one common realization. -/
lemma target_realized {n k : ℕ} (P : IntervalOracle.Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k) (href : References store (Core.Memo.remove K i p) s) :
    Core.target (Core.Memo.restrict R.costs K) i p (s.realize R (Core.Memo.remove K i p)) =
      realizedCost R.scale (target frame K i p s) := by
  classical
  let C := Core.Memo.restrict R.costs K
  let old := s.realize R (Core.Memo.remove K i p)
  have hv (q : Fin k) : C.cost i (p.succAbove q) (old.endpoint q) =
      realizedCost R.scale ((s.endpoint q).formal (K.1 i)) := by
    exact R.value (K.1 i) ((Core.Memo.remove K i p).2 q) (s.endpoint q) (href q)
  by_cases h : (Finset.univ : Finset (Fin k)).Nonempty
  · obtain ⟨q, hq, hmin⟩ := target_attained frame K i p s h
    have hnumeric : ∀ r, C.cost i (p.succAbove q) (old.endpoint q) ≤
        C.cost i (p.succAbove r) (old.endpoint r) := by
      intro r
      exact (R.compare (K.1 i) ((Core.Memo.remove K i p).2 q) (s.endpoint q) (href q)
        (K.1 i) ((Core.Memo.remove K i p).2 r) (s.endpoint r) (href r)).2.2.mp (hmin r)
    have hmin_eq : Core.target C i p old = C.cost i (p.succAbove q) (old.endpoint q) := by
      rw [Core.target, dite_eq_left h]
      exact le_antisymm (Finset.inf'_le _ (Finset.mem_univ q))
        (Finset.le_inf' h _ (fun r _ => hnumeric r))
    change Core.target C i p old = _
    rw [hmin_eq, hq, hv]
  · rw [Core.target, dite_eq_right h, target, dite_eq_right h]
    have hvwhole := R.value (K.1 i) (K.2 p) (frame.whole (K.2 p)) (whole_mem P frame store hvalid _)
    simpa only [Core.Memo.restrict, R.whole] using hvwhole

/-- The whole-parent branch has exactly the same truth value in both runs. -/
lemma whole_branch_iff {n k : ℕ} (P : IntervalOracle.Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (K : Core.Memo.Key n (k + 1))
    (i p : Fin (k + 1)) (s : State n k) (href : References store (Core.Memo.remove K i p) s) :
    recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s) ↔
      (Core.Memo.restrict R.costs K).cost i p 1 ≤
        Core.target (Core.Memo.restrict R.costs K) i p (s.realize R (Core.Memo.remove K i p)) := by
  obtain ⟨q, r, hr, ht⟩ := target_existing_record P frame store hvalid K i p s href
  have h := (R.compare (K.1 i) (K.2 p) (frame.whole (K.2 p)) (whole_mem P frame store hvalid _)
    (K.1 i) q r hr).2.2
  rw [target_realized P hvalid R K i p s href, ht]
  simpa only [Core.Memo.restrict, R.whole, R.value (K.1 i) q r hr] using h

/-- A physical record that copied the formal target becomes the unique legal
hungry root, for every ordinary hungry trim selector. -/
lemma candidate_coordinate_eq {n k : ℕ} (P : IntervalOracle.Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (K : Core.Memo.Key n (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (hcut : Core.CutSpec (Core.Memo.restrict R.costs K) cut)
    (i p : Fin (k + 1)) (s : State n k) (href : References store (Core.Memo.remove K i p) s)
    (r : Record n) (hr : r ∈ store (K.2 p))
    (hwhole : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s) → r = frame.whole (K.2 p))
    (htrim : ¬recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s) →
      r.formal (K.1 i) = target frame K i p s) :
    R.coordinate (K.2 p) r = Core.candidateEndpoint (Core.Memo.restrict R.costs K) cut i p
      (s.realize R (Core.Memo.remove K i p)) := by
  classical
  let C := Core.Memo.restrict R.costs K
  let old := s.realize R (Core.Memo.remove K i p)
  have hold : Core.Feasible old := s.realize_feasible R _ href
  by_cases hw : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s)
  · have hc := (whole_branch_iff P hvalid R K i p s href).mp hw
    rw [hwhole hw, R.whole, Core.candidateEndpoint, ite_eq_left hc]
  · have hc : ¬C.cost i p 1 ≤ Core.target C i p old :=
      fun h => hw ((whole_branch_iff P hvalid R K i p s href).mpr h)
    have ht0 := Core.target_nonnegative C i p old hold
    have ht1 : Core.target C i p old ≤ C.cost i p 1 := (lt_of_not_ge hc).le
    have hroot := hcut i p (Core.target C i p old) ht0 ht1
    have hvalue : C.cost i p (R.coordinate (K.2 p) r) = Core.target C i p old := by
      rw [target_realized P hvalid R K i p s href]
      exact (R.value (K.1 i) (K.2 p) r hr).trans (congrArg (realizedCost R.scale) (htrim hw))
    change R.coordinate (K.2 p) r = Core.candidateEndpoint C cut i p old
    rw [Core.candidateEndpoint, ite_eq_right hc]
    exact (C.strict i p).injOn (R.feasible _ _ hr) hroot.1 (hvalue.trans hroot.2.symm)

/-- The entire checked candidate, including its failure branch, is reproduced
by the ordinary hungry search under the common final-store realization. -/
theorem checked_candidate_replay {n k : ℕ} (P : IntervalOracle.Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (K : Core.Memo.Key n (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (hcut : Core.CutSpec (Core.Memo.restrict R.costs K) cut)
    (i p : Fin (k + 1)) (s : State n k) (href : References store (Core.Memo.remove K i p) s)
    (r : Record n) (hr : r ∈ store (K.2 p))
    (hwhole : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s) → r = frame.whole (K.2 p))
    (htrim : ¬recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s) →
      r.formal (K.1 i) = target frame K i p s) :
    (checked K (extendState i p s r)).map (fun out => out.realize R K) =
      Core.checkedCandidate (Core.Memo.restrict R.costs K) cut i p
        (s.realize R (Core.Memo.remove K i p)) := by
  classical
  let candidate := extendState i p s r
  have href' : References store K candidate :=
    extend_references store store (fun _ => List.Sublist.refl _) K i p s r href hr
  have hreal : candidate.realize R K = Core.candidate (Core.Memo.restrict R.costs K) cut i p
      (s.realize R (Core.Memo.remove K i p)) := by
    rw [show candidate = extendState i p s r from rfl, realize_extend,
      candidate_coordinate_eq P hvalid R K cut hcut i p s href r hr hwhole htrim]
    rfl
  have hfeas := candidate.realize_feasible R K href'
  have hEF := candidate.realize_envyFree_iff R K href'
  change (checked K candidate).map (fun out => out.realize R K) = _
  simp only [checked, Core.checkedCandidate, ← hreal, hfeas, true_and, hEF]
  split_ifs <;> rfl

end EnvyFreeResearch.Full.Chores.PhysicalCore
