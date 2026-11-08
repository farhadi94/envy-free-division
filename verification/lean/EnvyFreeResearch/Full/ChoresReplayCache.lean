import EnvyFreeResearch.Full.ChoresReplayExecution

/-!
# One simultaneous replay of the complete physical balanced-subset cache

The actual shared record store is threaded through all stages and all layers.
Its single final hungry realization reproduces every materialized cache value,
including missing entries, via the same fixed candidate order. This is the
operational replay step; no successful-cache premise is imposed.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent

def realizeCache {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (cache : Cache n k) : Core.Memo.Cache n k :=
  cache.map (fun entry => (entry.1, entry.2.map (fun s => s.realize R entry.1)))

lemma lookup_realizeCache {n k : ℕ} {frame : Frame n} {store : Store n}
    (R : StoreRealization frame store) (cache : Cache n k) (K : Core.Memo.Key n k) :
    Core.Memo.lookup (realizeCache R cache) K = (lookup cache K).map (fun s => s.realize R K) := by
  classical
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨L, value⟩ := entry
    by_cases heq : K = L
    · subst K
      simp only [realizeCache, List.map_cons, lookup, Core.Memo.lookup, ite_true]
    · simp only [realizeCache, List.map_cons, lookup, Core.Memo.lookup, ite_eq_right heq]
      exact ih

lemma keys_run_properties {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (previous : Cache n k) (hprevious : CacheValid store previous)
    (keys : List (Core.Memo.Key n (k + 1))) (prior : History (Query (Fin n)) ℝ)
    (result : LayerResult n (k + 1)) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (keysProgram frame store previous keys) prior result trace) :
    ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      CacheValid result.store result.cache ∧ result.cache.map Prod.fst = keys := by
  obtain ⟨result', trace', hexec, _, _, hvalid', hkeep, hcache, hkeys⟩ := keys_program_correct
    P hmono oracle hpolicy frame store hvalid hzero previous hprevious keys prior
  obtain ⟨rfl, _⟩ := hrun.deterministic hexec
  exact ⟨hvalid', hkeep, hcache, hkeys⟩

lemma layers_run_properties {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (k : ℕ) (prior : History (Query (Fin n)) ℝ)
    (result : LayerResult n k) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (layersProgram frame store k) prior result trace) :
    ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      CacheValid result.store result.cache ∧
      result.cache.map Prod.fst = (Finset.univ : Finset (Core.Memo.Key n k)).toList := by
  obtain ⟨result', trace', hexec, _, _, hvalid', hkeep, hcache, hkeys⟩ := layers_program_correct
    P hmono oracle hpolicy frame store hvalid hzero k prior
  obtain ⟨rfl, _⟩ := hrun.deterministic hexec
  exact ⟨hvalid', hkeep, hcache, hkeys⟩

/-- The physical traversal of a layer is reproduced by the hungry stage on the
realized previous cache, with every key represented exactly once. -/
theorem keys_program_replay {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store finalStore : Store n)
    (hvalid : ValidStore P frame store) (hfinalValid : ValidStore P frame finalStore)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hkeep : ∀ q, (store q).Sublist (finalStore q))
    (R : StoreRealization frame finalStore) (cut : Fin n → Fin n → ℝ → ℝ)
    (hcut : Core.CutSpec R.costs cut)
    (previous : Cache n k) (hprevious : CacheValid store previous)
    (keys : List (Core.Memo.Key n (k + 1))) (prior : History (Query (Fin n)) ℝ)
    (result : LayerResult n (k + 1)) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (keysProgram frame store previous keys) prior result trace)
    (hresultKeep : ∀ q, (result.store q).Sublist (finalStore q)) :
    realizeCache R result.cache = keys.map (fun K => (K,
      Core.searchStage (Core.Memo.restrict R.costs K) (fun i p t => cut (K.1 i) (K.2 p) t)
        (fun i p => Core.Memo.lookup (realizeCache R previous) (Core.Memo.remove K i p)))) := by
  classical
  induction keys generalizing store prior result trace with
  | nil =>
    change Executes oracle (.returned ⟨store, []⟩) prior result trace at hrun
    cases hrun
    rfl
  | cons K rest ih =>
    rw [keysProgram] at hrun
    obtain ⟨first, firstTrace, following, hfirst, hfollowing, _⟩ := hrun.split_bind _ _
    obtain ⟨tail, tailTrace, lastTrace, htail, hreturn, _⟩ := hfollowing.split_bind _ _
    cases hreturn
    have hsmall : ∀ i p s, lookup previous (Core.Memo.remove K i p) = some s →
        References store (Core.Memo.remove K i p) s :=
      fun i p s hs => (lookup_sound store previous hprevious _ s hs).1
    obtain ⟨hfirstValid, hfirstKeep, _⟩ := trials_run_properties P hmono oracle hpolicy frame store hvalid
      hzero K _ hsmall (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).toList prior first firstTrace hfirst
    have hprevious' := hprevious.mono hfirstKeep
    obtain ⟨_, htailKeep, _, _⟩ := keys_run_properties P hmono oracle hpolicy frame first.store hfirstValid
      hzero previous hprevious' rest (prior ++ firstTrace) tail tailTrace htail
    have hfirstFinal : ∀ q, (first.store q).Sublist (finalStore q) :=
      fun q => (htailKeep q).trans (hresultKeep q)
    have hlocal : Core.CutSpec (Core.Memo.restrict R.costs K) (fun i p t => cut (K.1 i) (K.2 p) t) := by
      intro i p t ht0 ht1
      exact hcut _ _ _ ht0 ht1
    have hreplayFirst := stage_program_replay P hmono oracle hpolicy frame store finalStore hvalid hfinalValid
      hzero hkeep R K _ hlocal _ hsmall prior first firstTrace hfirst hfirstFinal
    have hreplayTail := ih first.store hfirstValid hfirstFinal hprevious' (prior ++ firstTrace)
      tail tailTrace htail hresultKeep
    change (K, first.output.map (fun s => s.realize R K)) :: realizeCache R tail.cache = _
    rw [List.map_cons, hreplayTail]
    congr 2
    simpa only [lookup_realizeCache] using hreplayFirst

/-- The entire actual nonhungry physical program replays on one constructed
hungry profile. The claim includes every materialized layer and all previous
failures; it does not assume any previous cache state succeeded. -/
theorem layers_program_replay {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store finalStore : Store n)
    (hvalid : ValidStore P frame store) (hfinalValid : ValidStore P frame finalStore)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (_hkeep : ∀ q, (store q).Sublist (finalStore q))
    (R : StoreRealization frame finalStore) (cut : Fin n → Fin n → ℝ → ℝ)
    (hcut : Core.CutSpec R.costs cut) (k : ℕ) (prior : History (Query (Fin n)) ℝ)
    (result : LayerResult n k) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (layersProgram frame store k) prior result trace)
    (hresultKeep : ∀ q, (result.store q).Sublist (finalStore q)) :
    realizeCache R result.cache = Core.Memo.layers R.costs cut k := by
  classical
  induction k generalizing trace with
  | zero =>
    change Executes oracle (.returned ⟨store, (Finset.univ : Finset (Core.Memo.Key n 0)).toList.map
      (fun K => (K, some ⟨Fin.elim0, Equiv.refl _⟩))⟩) prior result trace at hrun
    cases hrun
    have hempty (K : Core.Memo.Key n 0) :
        (⟨Fin.elim0, Equiv.refl _⟩ : State n 0).realize R K =
          (⟨Fin.elim0, Equiv.refl _⟩ : Core.State 0) := by
      unfold State.realize
      congr 1
      funext p
      exact Fin.elim0 p
    simp only [realizeCache, Core.Memo.layers, List.map_map, Function.comp_def, Option.map_some, hempty]
  | succ k ih =>
    rw [layersProgram] at hrun
    obtain ⟨previous, firstTrace, tailTrace, hfirst, htail, _⟩ := hrun.split_bind _ _
    obtain ⟨hfirstValid, hfirstKeep, hfirstCache, _⟩ := layers_run_properties P hmono oracle hpolicy
      frame store hvalid hzero k prior previous firstTrace hfirst
    obtain ⟨_, htailKeep, _, _⟩ := keys_run_properties P hmono oracle hpolicy frame previous.store hfirstValid
      hzero previous.cache hfirstCache _ (prior ++ firstTrace) result tailTrace htail
    have hfirstFinal : ∀ q, (previous.store q).Sublist (finalStore q) :=
      fun q => (htailKeep q).trans (hresultKeep q)
    have hreplayFirst := ih previous firstTrace hfirst hfirstFinal
    have hreplayTail := keys_program_replay P hmono oracle hpolicy frame previous.store finalStore
      hfirstValid hfinalValid hzero hfirstFinal R cut hcut previous.cache hfirstCache _
      (prior ++ firstTrace) result tailTrace htail hresultKeep
    rw [hreplayTail, hreplayFirst]
    rfl

end EnvyFreeResearch.Full.Chores.PhysicalCore
