import EnvyFreeResearch.Full.ChoresPhysicalStages

/-!
# Materialized balanced-subset cache with actual physical query execution

Every stage reads the previous materialized layer and updates one shared
persistent store. The table and all failed-candidate records are preserved
through the complete finite traversal. These theorems establish physical
termination, trace bounds and partial EF correctness; nonhungry success is the
remaining global finite-realization replay theorem.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped BigOperators

abbrev Cache (n k : ℕ) := List (Core.Memo.Key n k × Option (State n k))

def lookup {n k : ℕ} (cache : Cache n k) (K : Core.Memo.Key n k) : Option (State n k) := by
  classical
  exact match cache with
  | [] => none
  | (L, value) :: rest => if K = L then value else lookup rest K

def CacheValid {n k : ℕ} (store : Store n) (cache : Cache n k) : Prop :=
  ∀ entry ∈ cache, ∀ s, entry.2 = some s → References store entry.1 s ∧ EnvyFree entry.1 s

lemma CacheValid.mono {n k : ℕ} {oldStore newStore : Store n} {cache : Cache n k}
    (hcache : CacheValid oldStore cache) (hkeep : ∀ p, (oldStore p).Sublist (newStore p)) :
    CacheValid newStore cache := by
  intro entry he s hs
  exact ⟨(hcache entry he s hs).1.mono hkeep, (hcache entry he s hs).2⟩

lemma lookup_sound {n k : ℕ} (store : Store n) (cache : Cache n k)
    (hcache : CacheValid store cache) (K : Core.Memo.Key n k) (s : State n k)
    (h : lookup cache K = some s) : References store K s ∧ EnvyFree K s := by
  classical
  induction cache with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
    obtain ⟨L, value⟩ := entry
    change (if K = L then value else lookup rest K) = some s at h
    by_cases heq : K = L
    · subst K
      rw [ite_eq_left rfl] at h
      exact hcache (L, value) List.mem_cons_self s h
    · rw [ite_eq_right heq] at h
      exact ih (fun entry he => hcache entry (List.mem_cons_of_mem _ he)) h

structure LayerResult (n k : ℕ) where
  store : Store n
  cache : Cache n k

/-- Singleton parents are selected whole and make no physical request. -/
lemma trial_singleton_returned {n : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n 1) (i p : Fin 1) (old : Option (State n 0)) :
    ∃ out, trialProgram frame store K i p old = Program.returned ⟨store, out⟩ := by
  classical
  cases old with
  | none => exact ⟨none, rfl⟩
  | some s =>
    refine ⟨checked K (extendState i p s (frame.whole (K.2 p))), ?_⟩
    simp [trialProgram, target, recordLE]

lemma trials_singleton_returned {n : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n 1) (smaller : Fin 1 → Fin 1 → Option (State n 0))
    (trials : List (Fin 1 × Fin 1)) :
    ∃ out, trialsProgram frame store K smaller trials = Program.returned ⟨store, out⟩ := by
  induction trials with
  | nil => exact ⟨none, rfl⟩
  | cons ip rest ih =>
    obtain ⟨out, hout⟩ := trial_singleton_returned frame store K ip.1 ip.2 (smaller ip.1 ip.2)
    obtain ⟨tail, htail⟩ := ih
    refine ⟨prefer out tail, ?_⟩
    rw [trialsProgram, hout, Program.bind, htail, Program.bind]

lemma singleton_stage_trace_empty {n : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n 1) (smaller : Fin 1 → Fin 1 → Option (State n 0))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (prior : History (Query (Fin n)) ℝ)
    (result : TrialResult n 1) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (stageProgram frame store K smaller) prior result trace) : trace = [] := by
  obtain ⟨out, hout⟩ := trials_singleton_returned frame store K smaller
    (Finset.univ : Finset (Fin 1 × Fin 1)).toList
  change Executes oracle (trialsProgram frame store K smaller _) prior result trace at h
  rw [hout] at h
  cases h
  rfl

def stageWeight (k : ℕ) : ℕ := if k = 0 then 0 else (k + 1) ^ 2

lemma stage_program_exact_bound {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hsmaller : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : TrialResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (stageProgram frame store K smaller) prior result trace ∧
      trace.length ≤ n * stageWeight k ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ stageWeight k ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  obtain ⟨result, trace, hexec, hlen, hcuts, hvalid', hkeep, hout⟩ := stage_program_correct
    P hmono oracle hpolicy frame store hvalid hzero K smaller hsmaller prior
  refine ⟨result, trace, hexec, ?_, ?_, hvalid', hkeep, hout⟩
  · by_cases hk : k = 0
    · subst k
      rw [singleton_stage_trace_empty frame store K smaller oracle prior result trace hexec]
      simp
    · simpa only [stageWeight, ite_eq_right hk] using hlen
  · by_cases hk : k = 0
    · subst k
      rw [singleton_stage_trace_empty frame store K smaller oracle prior result trace hexec]
      simp
    · simpa only [stageWeight, ite_eq_right hk] using hcuts

/-- The physical layer visits each supplied key once and shares one immutable
previous layer, with the current global record store threaded through it. -/
def keysProgram {n k : ℕ} (frame : Frame n) (store : Store n) (previous : Cache n k) :
    List (Core.Memo.Key n (k + 1)) → Program (Query (Fin n)) ℝ (LayerResult n (k + 1))
  | [] => .returned ⟨store, []⟩
  | K :: rest => (stageProgram frame store K (fun i p => lookup previous (Core.Memo.remove K i p))).bind
      (fun stage => (keysProgram frame stage.store previous rest).bind (fun tail =>
        .returned ⟨tail.store, (K, stage.output) :: tail.cache⟩))

theorem keys_program_correct {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (previous : Cache n k) (hprevious : CacheValid store previous)
    (keys : List (Core.Memo.Key n (k + 1))) (prior : History (Query (Fin n)) ℝ) :
    ∃ result : LayerResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (keysProgram frame store previous keys) prior result trace ∧
      trace.length ≤ n * stageWeight k * keys.length ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ stageWeight k * keys.length ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      CacheValid result.store result.cache ∧ result.cache.map Prod.fst = keys := by
  classical
  induction keys generalizing store prior with
  | nil =>
    refine ⟨⟨store, []⟩, [], Executes.returned _ _, by simp, by simp, hvalid,
      fun _ => List.Sublist.refl _, ?_, rfl⟩
    intro entry he
    cases he
  | cons K rest ih =>
    have hsmall : ∀ i p s, lookup previous (Core.Memo.remove K i p) = some s →
        References store (Core.Memo.remove K i p) s :=
      fun i p s hs => (lookup_sound store previous hprevious _ s hs).1
    obtain ⟨first, firstTrace, hfirst, hfirstLen, hfirstCuts, hfirstStore, hfirstKeep, hfirstOut⟩ :=
      stage_program_exact_bound P hmono oracle hpolicy frame store hvalid hzero K _ hsmall prior
    obtain ⟨tail, tailTrace, htail, htailLen, htailCuts, htailStore, htailKeep, htailCache, htailKeys⟩ :=
      ih first.store hfirstStore (hprevious.mono hfirstKeep) (prior ++ firstTrace)
    let result : LayerResult n (k + 1) := ⟨tail.store, (K, first.output) :: tail.cache⟩
    have htail' : Executes oracle
        ((keysProgram frame first.store previous rest).bind (fun tail =>
          .returned (⟨tail.store, (K, first.output) :: tail.cache⟩ : LayerResult n (k + 1))))
        (prior ++ firstTrace) result tailTrace := by
      simpa only [List.append_nil] using htail.bind (fun tail => Program.returned
        (⟨tail.store, (K, first.output) :: tail.cache⟩ : LayerResult n (k + 1)))
        (Executes.returned result ((prior ++ firstTrace) ++ tailTrace))
    have hexec : Executes oracle (keysProgram frame store previous (K :: rest)) prior result
        (firstTrace ++ tailTrace) :=
      hfirst.bind (fun stage => (keysProgram frame stage.store previous rest).bind (fun tail =>
        .returned (⟨tail.store, (K, stage.output) :: tail.cache⟩ : LayerResult n (k + 1)))) htail'
    refine ⟨result, firstTrace ++ tailTrace, hexec, ?_, ?_, htailStore,
      fun q => (hfirstKeep q).trans (htailKeep q), ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [List.countP_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro entry he s hs
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨(hfirstOut s hs).1.mono htailKeep, (hfirstOut s hs).2⟩
      · exact htailCache entry he s hs
    · change (K :: tail.cache.map Prod.fst) = K :: rest
      rw [htailKeys]

/-- The base layer is a materialized singleton empty-subset problem; every
successor materializes all balanced keys exactly once. -/
def layersProgram {n : ℕ} (frame : Frame n) (store : Store n) :
    (k : ℕ) → Program (Query (Fin n)) ℝ (LayerResult n k)
  | 0 => .returned ⟨store, (Finset.univ : Finset (Core.Memo.Key n 0)).toList.map
      (fun K => (K, some ⟨Fin.elim0, Equiv.refl _⟩))⟩
  | k + 1 => (layersProgram frame store k).bind (fun previous =>
      keysProgram frame previous.store previous.cache (Finset.univ : Finset (Core.Memo.Key n (k + 1))).toList)

/-- Exact prefix-table ledger: singleton layers are proved query-free. -/
def physicalBudget (n k : ℕ) : ℕ := ∑ j ∈ Finset.range k, stageWeight j * (n.choose (j + 1)) ^ 2

/-- The full finite physical table terminates and materializes each balanced
key once. Every stored successful entry is formally EF and refers to permanent
records in the final shared store. No success of a missing entry is assumed. -/
theorem layers_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (k : ℕ) (prior : History (Query (Fin n)) ℝ) :
    ∃ result : LayerResult n k, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (layersProgram frame store k) prior result trace ∧
      trace.length ≤ n * physicalBudget n k ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ physicalBudget n k ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      CacheValid result.store result.cache ∧
      result.cache.map Prod.fst = (Finset.univ : Finset (Core.Memo.Key n k)).toList := by
  classical
  induction k with
  | zero =>
    let cache : Cache n 0 := (Finset.univ : Finset (Core.Memo.Key n 0)).toList.map
      (fun K => (K, some ⟨Fin.elim0, Equiv.refl _⟩))
    refine ⟨⟨store, cache⟩, [], Executes.returned _ _, by simp [physicalBudget],
      by simp [physicalBudget], hvalid, fun _ => List.Sublist.refl _, ?_, ?_⟩
    · intro entry he s hs
      obtain ⟨K, _, heq⟩ := List.mem_map.mp he
      subst entry
      cases Option.some.inj hs
      exact ⟨fun p => Fin.elim0 p, fun i => Fin.elim0 i⟩
    · simp [cache, List.map_map, Function.comp_def]
  | succ k ih =>
    obtain ⟨previous, firstTrace, hfirst, hfirstLen, hfirstCuts, hfirstStore, hfirstKeep, hfirstCache, _⟩ := ih
    obtain ⟨result, tailTrace, htail, htailLen, htailCuts, htailStore, htailKeep, htailCache, hkeys⟩ :=
      keys_program_correct P hmono oracle hpolicy frame previous.store hfirstStore hzero previous.cache
        hfirstCache (Finset.univ : Finset (Core.Memo.Key n (k + 1))).toList (prior ++ firstTrace)
    have hlength : (Finset.univ : Finset (Core.Memo.Key n (k + 1))).toList.length =
        (n.choose (k + 1)) ^ 2 := by simp only [Finset.length_toList, Finset.card_univ, Core.Memo.key_card]
    rw [hlength] at htailLen htailCuts
    refine ⟨result, firstTrace ++ tailTrace,
      hfirst.bind (fun previous => keysProgram frame previous.store previous.cache
        (Finset.univ : Finset (Core.Memo.Key n (k + 1))).toList) htail,
      ?_, ?_, htailStore, fun q => (hfirstKeep q).trans (htailKeep q), htailCache, hkeys⟩
    · simp only [List.length_append, physicalBudget, Finset.sum_range_succ, Nat.mul_add]
      change firstTrace.length + tailTrace.length ≤ n * physicalBudget n k +
        n * (stageWeight k * (n.choose (k + 1)) ^ 2)
      nlinarith only [hfirstLen, htailLen]
    · simp only [List.countP_append, physicalBudget, Finset.sum_range_succ]
      exact Nat.add_le_add hfirstCuts htailCuts

lemma physicalBudget_eq (n k : ℕ) : physicalBudget n k =
    ∑ j ∈ Finset.range (k - 1), (j + 2) ^ 2 * (n.choose (j + 2)) ^ 2 := by
  cases k with
  | zero => simp [physicalBudget]
  | succ k =>
    rw [physicalBudget, Finset.sum_range_succ']
    simp only [stageWeight, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      ite_true, zero_mul, add_zero, Nat.add_sub_cancel, Nat.add_assoc]

/-- The complete physical prefix-table trace has the manuscript's exact `T_n`
trim bound, with the enclosing-observer recording factor for total queries.
All cache candidates are executed, including all failed ones. -/
theorem full_physical_table_bound {n : ℕ} (hn : 0 < n) (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0)) :
    ∃ result : LayerResult n n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (layersProgram frame store n).protocol oracle ()
        (n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1))) [] = ⟨trace, .returned result⟩ ∧
      trace.length ≤ n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) ∧
      ValidStore P frame result.store ∧ CacheValid result.store result.cache ∧
      result.cache.map Prod.fst = (Finset.univ : Finset (Core.Memo.Key n n)).toList := by
  obtain ⟨result, trace, hexec, hlen, hcuts, hvalid', _, hcache, hkeys⟩ :=
    layers_program_correct P hmono oracle hpolicy frame store hvalid hzero n []
  have hbudget : physicalBudget n n = n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) := by
    rw [physicalBudget_eq]
    exact EnvyFreeResearch.R6Core.core_transition_closed n hn
  rw [hbudget] at hlen hcuts
  exact ⟨result, trace, hexec.run _ hlen, hlen, hcuts, hvalid', hcache, hkeys⟩

end EnvyFreeResearch.Full.Chores.PhysicalCore
