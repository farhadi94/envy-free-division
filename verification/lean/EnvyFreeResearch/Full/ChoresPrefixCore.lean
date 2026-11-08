import EnvyFreeResearch.Full.ChoresReplayCache

/-!
# Unconditional physical prefix Core for arbitrary nonnegative costs

The actual memoized physical program succeeds for every legal adaptive reply
policy. Its complete final persistent table is realized once, the whole run is
replayed on that hungry profile, and unconditional hungry correctness excludes
all missing cache entries. The protocol never constructs or queries that
realization. Initial parent cutting and the outer chore scheduler are separate.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent

def Anchored {n k : ℕ} (frame : Frame n) (K : Core.Memo.Key n k) (s : State n k) : Prop :=
  ∃ rank : Fin k → ℕ, ∀ i,
    s.endpoint (s.matching i) = frame.whole (K.2 (s.matching i)) ∨
      ∃ j, rank j < rank i ∧ ((s.endpoint (s.matching j)).formal (K.1 i)) =
        ((s.endpoint (s.matching i)).formal (K.1 i))

lemma formal_record_injective {n : ℕ} (records : List (Record n))
    (horder : List.Pairwise Before records) (i : Fin n) (r s : Record n)
    (hr : r ∈ records) (hs : s ∈ records) (heq : r.formal i = s.formal i) : r = s := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hs
  rcases lt_trichotomy j k with h | h | h
  · have hlt := (horder.rel_get_of_lt h).2 i
    rw [hj, hk, heq] at hlt
    exact (recordLT_irrefl _ hlt).elim
  · exact hj.symm.trans ((congrArg records.get h).trans hk)
  · have hlt := (horder.rel_get_of_lt h).2 i
    rw [hj, hk, heq] at hlt
    exact (recordLT_irrefl _ hlt).elim

lemma coordinate_one_is_whole {n : ℕ} (P : Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (i p : Fin n) (r : Record n) (hr : r ∈ store p)
    (hone : R.coordinate p r = 1) : r = frame.whole p := by
  have hw := whole_mem P frame store hvalid p
  have heq : r.formal i = (frame.whole p).formal i :=
    (R.compare i p r hr i p (frame.whole p) hw).2.1.mpr (by rw [hone, R.whole])
  exact formal_record_injective (store p) (hvalid p).1 i r (frame.whole p) hr hw heq

lemma anchored_of_realized {n k : ℕ} (P : Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (R : StoreRealization frame store) (K : Core.Memo.Key n k) (s : State n k)
    (href : References store K s)
    (ha : Core.Anchored (Core.Memo.restrict R.costs K).cost (s.realize R K)) : Anchored frame K s := by
  obtain ⟨rank, hrank⟩ := ha
  refine ⟨rank, ?_⟩
  intro i
  rcases hrank i with hw | ⟨j, hj, heq⟩
  · exact Or.inl (coordinate_one_is_whole P hvalid R (K.1 i) (K.2 (s.matching i))
      (s.endpoint (s.matching i)) (href _) hw)
  · exact Or.inr ⟨j, hj, (R.compare (K.1 i) (K.2 (s.matching j)) (s.endpoint (s.matching j)) (href _)
      (K.1 i) (K.2 (s.matching i)) (s.endpoint (s.matching i)) (href _)).2.1.mpr heq⟩

lemma anchored_has_whole {n k : ℕ} (hk : 0 < k) (frame : Frame n)
    (K : Core.Memo.Key n k) (s : State n k) (ha : Anchored frame K s) :
    ∃ i, s.endpoint (s.matching i) = frame.whole (K.2 (s.matching i)) := by
  classical
  obtain ⟨rank, hrank⟩ := ha
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ rank hne
  rcases hrank i with hw | ⟨j, hj, _⟩
  · exact ⟨i, hw⟩
  · exact (not_lt_of_ge (hi j (Finset.mem_univ j)) hj).elim

/-- The complete simultaneous replay rules out every missing subset entry,
for arbitrary nonnegative profiles and arbitrary full-history legal replies. -/
theorem physical_cache_complete {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hproper : ∀ p, frame.empty p ≠ frame.whole p)
    (k : ℕ) (prior : History (Query (Fin n)) ℝ)
    (result : LayerResult n k) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (layersProgram frame store k) prior result trace) :
    ∀ K : Core.Memo.Key n k, ∃ s : State n k,
      lookup result.cache K = some s ∧ References result.store K s ∧ EnvyFree K s ∧ Anchored frame K s := by
  classical
  obtain ⟨hfinalValid, hkeep, hcache, _⟩ := layers_run_properties P hmono oracle hpolicy frame store hvalid
    hzero k prior result trace hrun
  obtain ⟨R⟩ := exists_store_realization P frame result.store hfinalValid hzero hproper
  obtain ⟨cut, hcut⟩ := Core.exists_cut_selector R.costs
  have hreplay := layers_program_replay P hmono oracle hpolicy frame store result.store hvalid hfinalValid
    hzero hkeep R cut hcut k prior result trace hrun (fun _ => List.Sublist.refl _)
  intro K
  obtain ⟨u, hu, _, _, hau⟩ := Core.Memo.every_lookup_succeeds n k R.costs cut hcut K
  have hlookup := congrArg (fun cache => Core.Memo.lookup cache K) hreplay
  rw [lookup_realizeCache, hu] at hlookup
  cases hs : lookup result.cache K with
  | none => simp [hs] at hlookup
  | some s =>
    have hreal : s.realize R K = u := Option.some.inj (by simpa only [hs, Option.map_some] using hlookup)
    obtain ⟨href, hEF⟩ := lookup_sound result.store result.cache hcache K s hs
    refine ⟨s, rfl, href, hEF, ?_⟩
    apply anchored_of_realized P hfinalValid R K s href
    rw [hreal]
    exact hau

def fullKey (n : ℕ) : Core.Memo.Key n n := ((OrderIso.refl _).toOrderEmbedding, (OrderIso.refl _).toOrderEmbedding)

structure PrefixResult (n : ℕ) where
  store : Store n
  state : State n n

/-- A fixed physical prefix protocol returns the full population's successful
state after completing the shared table. The unreachable failure is explicit. -/
def prefixProgram {n : ℕ} (frame : Frame n) (store : Store n) :
    Program (Query (Fin n)) ℝ (PrefixResult n) :=
  (layersProgram frame store n).bind (fun result => match lookup result.cache (fullKey n) with
    | none => .failed
    | some s => .returned ⟨result.store, s⟩)

/-- Unconditional physical prefix-Core correctness and the exact ordinary
query ledger, under every legal adaptive Cut policy. Every allocated prefix is
from a distinct input parent and at least one is literally the whole record. -/
theorem prefix_program_correct {n : ℕ} (hn : 0 < n) (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hproper : ∀ p, frame.empty p ≠ frame.whole p) :
    ∃ result : PrefixResult n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (prefixProgram frame store).protocol oracle ()
        (n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1))) [] = ⟨trace, .returned result⟩ ∧
      trace.length ≤ n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) ∧
      ValidStore P frame result.store ∧ References result.store (fullKey n) result.state ∧
      EnvyFree (fullKey n) result.state ∧ Anchored frame (fullKey n) result.state ∧
      ∃ i, result.state.endpoint (result.state.matching i) = frame.whole (result.state.matching i) := by
  obtain ⟨table, trace, hexec, hlen, hcuts, hvalid', _, _, _⟩ :=
    layers_program_correct P hmono oracle hpolicy frame store hvalid hzero n []
  obtain ⟨s, hs, href, hEF, ha⟩ := physical_cache_complete P hmono oracle hpolicy frame store hvalid hzero
    hproper n [] table trace hexec (fullKey n)
  let result : PrefixResult n := ⟨table.store, s⟩
  have hfinish : Executes oracle
      (match lookup table.cache (fullKey n) with
        | none => Program.failed
        | some s => Program.returned (⟨table.store, s⟩ : PrefixResult n))
      ([] ++ trace) result [] := by
    rw [hs]
    exact Executes.returned result _
  have hprogram : Executes oracle (prefixProgram frame store) [] result trace := by
    simpa only [prefixProgram, List.append_nil] using hexec.bind (fun result =>
      match lookup result.cache (fullKey n) with
      | none => Program.failed
      | some s => Program.returned (⟨result.store, s⟩ : PrefixResult n)) hfinish
  have hbudget : physicalBudget n n = n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) := by
    rw [physicalBudget_eq]
    exact EnvyFreeResearch.R6Core.core_transition_closed n hn
  rw [hbudget] at hlen hcuts
  exact ⟨result, trace, hprogram.run _ hlen, hlen, hcuts, hvalid', href, hEF, ha,
    by simpa [result, fullKey] using anchored_has_whole hn frame (fullKey n) s ha⟩

end EnvyFreeResearch.Full.Chores.PhysicalCore
