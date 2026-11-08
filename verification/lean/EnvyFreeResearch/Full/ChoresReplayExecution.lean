import EnvyFreeResearch.Full.ChoresReplayGeometry

/-!
# Replay of actual physical Core executions

Operational properties are derived from the constructed physical programs and
determinism of the actual full-history policy. One realization of the final
store reproduces the output of every candidate, including rejected candidates.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent

lemma trial_run_properties {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (old : Option (State n k))
    (hold : ∀ s, old = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) (result : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (trialProgram frame store K i p old) prior result trace) :
    ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  obtain ⟨result', trace', hexec, _, _, hvalid', hkeep, hout⟩ := trial_program_correct
    P hmono oracle hpolicy frame store hvalid hzero K i p old hold prior
  obtain ⟨rfl, _⟩ := hrun.deterministic hexec
  exact ⟨hvalid', hkeep, hout⟩

lemma trials_run_properties {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hold : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (trials : List (Fin (k + 1) × Fin (k + 1))) (prior : History (Query (Fin n)) ℝ)
    (result : TrialResult n (k + 1)) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (trialsProgram frame store K smaller trials) prior result trace) :
    ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  obtain ⟨result', trace', hexec, _, _, hvalid', hkeep, hout⟩ := trials_program_correct
    P hmono oracle hpolicy frame store hvalid hzero K smaller hold trials prior
  obtain ⟨rfl, _⟩ := hrun.deterministic hexec
  exact ⟨hvalid', hkeep, hout⟩

/-- A completed physical trial is replayed exactly by the hungry candidate
checker, using one common final-store realization and any hungry trim selector. -/
theorem trial_program_replay {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store finalStore : Store n)
    (hvalid : ValidStore P frame store) (hfinalValid : ValidStore P frame finalStore)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hkeep : ∀ q, (store q).Sublist (finalStore q))
    (R : StoreRealization frame finalStore) (K : Core.Memo.Key n (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (hcut : Core.CutSpec (Core.Memo.restrict R.costs K) cut)
    (i p : Fin (k + 1)) (old : Option (State n k))
    (hold : ∀ s, old = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) (result : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (trialProgram frame store K i p old) prior result trace)
    (hresultKeep : ∀ q, (result.store q).Sublist (finalStore q)) :
    result.output.map (fun s => s.realize R K) =
      (old.map (fun s => s.realize R (Core.Memo.remove K i p))).bind
        (Core.checkedCandidate (Core.Memo.restrict R.costs K) cut i p) := by
  classical
  cases old with
  | none =>
    change Executes oracle (.returned ⟨store, none⟩) prior result trace at hrun
    cases hrun
    rfl
  | some s =>
    have href := hold s rfl
    have hrefFinal := href.mono hkeep
    let t := target frame K i p s
    by_cases hwhole : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) t
    · have hprogram : trialProgram frame store K i p (some s) =
          .returned ⟨store, checked K (extendState i p s (frame.whole (K.2 p)))⟩ := by
        simp only [trialProgram, t, ite_eq_left hwhole]
      rw [hprogram] at hrun
      cases hrun
      exact checked_candidate_replay P hfinalValid R K cut hcut i p s hrefFinal
        (frame.whole (K.2 p)) (whole_mem P frame finalStore hfinalValid _) (fun _ => rfl)
        (fun h => (h hwhole).elim)
    · have hlow : recordLE ((frame.empty (K.2 p)).formal (K.1 i)) t := by
        rw [hzero]
        exact target_nonnegative P frame store hvalid hzero K i p s href
      have hhigh : recordLE t ((frame.whole (K.2 p)).formal (K.1 i)) :=
        Or.inl (target_lt_whole frame K i p s hwhole)
      have hprogram : trialProgram frame store K i p (some s) =
          (ensureGlobalProgram store (K.1 i) (K.2 p) t).bind (fun out =>
            .returned ⟨out.store, checked K (extendState i p s out.selected)⟩) := by
        simp only [trialProgram, t, ite_eq_right hwhole]
      rw [hprogram] at hrun
      obtain ⟨operation, first, second, hoperation, hreturn, _⟩ := hrun.split_bind _ _
      obtain ⟨operation', trace', hexec, _, _, _, _, _, hselected, hcopy⟩ :=
        ensure_global_program_correct P hmono oracle hpolicy frame store hvalid (K.1 i) (K.2 p) t hlow hhigh prior
      obtain ⟨rfl, _⟩ := hoperation.deterministic hexec
      cases hreturn
      apply checked_candidate_replay P hfinalValid R K cut hcut i p s hrefFinal operation.selected
        ((hresultKeep _).subset hselected)
      · intro h
        exact (hwhole h).elim
      · intro _
        exact hcopy

lemma prefer_map {A B : Type*} (f : A → B) (first second : Option A) :
    (prefer first second).map f = prefer (first.map f) (second.map f) := by cases first <;> rfl

lemma firstSome_cons {A : Type*} (a : Option A) (tail : List (Option A)) :
    Core.firstSome (a :: tail) = prefer a (Core.firstSome tail) := by cases a <;> rfl

/-- A complete sequential candidate stage, including every failure and every
later exploratory query, has exactly the hungry first-success result under
one realization of its final retained table. -/
theorem trials_program_replay {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store finalStore : Store n)
    (hvalid : ValidStore P frame store) (hfinalValid : ValidStore P frame finalStore)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hkeep : ∀ q, (store q).Sublist (finalStore q))
    (R : StoreRealization frame finalStore) (K : Core.Memo.Key n (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (hcut : Core.CutSpec (Core.Memo.restrict R.costs K) cut)
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hold : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (trials : List (Fin (k + 1) × Fin (k + 1))) (prior : History (Query (Fin n)) ℝ)
    (result : TrialResult n (k + 1)) (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (trialsProgram frame store K smaller trials) prior result trace)
    (hresultKeep : ∀ q, (result.store q).Sublist (finalStore q)) :
    result.output.map (fun s => s.realize R K) = Core.firstSome (trials.map (fun ip =>
      ((smaller ip.1 ip.2).map (fun s => s.realize R (Core.Memo.remove K ip.1 ip.2))).bind
        (Core.checkedCandidate (Core.Memo.restrict R.costs K) cut ip.1 ip.2))) := by
  classical
  induction trials generalizing store prior result trace with
  | nil =>
    change Executes oracle (.returned ⟨store, none⟩) prior result trace at hrun
    cases hrun
    rfl
  | cons ip rest ih =>
    rw [trialsProgram] at hrun
    obtain ⟨first, firstTrace, following, hfirst, hfollowing, _⟩ := hrun.split_bind _ _
    obtain ⟨tail, tailTrace, lastTrace, htail, hreturn, _⟩ := hfollowing.split_bind _ _
    cases hreturn
    obtain ⟨hfirstValid, hfirstKeep, _⟩ := trial_run_properties P hmono oracle hpolicy frame store hvalid
      hzero K ip.1 ip.2 (smaller ip.1 ip.2) (hold ip.1 ip.2) prior first firstTrace hfirst
    have hsmall' : ∀ i p s, smaller i p = some s → References first.store (Core.Memo.remove K i p) s :=
      fun i p s hs => (hold i p s hs).mono hfirstKeep
    obtain ⟨_, htailKeep, _⟩ := trials_run_properties P hmono oracle hpolicy frame first.store hfirstValid
      hzero K smaller hsmall' rest (prior ++ firstTrace) tail tailTrace htail
    have hfirstFinal : ∀ q, (first.store q).Sublist (finalStore q) :=
      fun q => (htailKeep q).trans (hresultKeep q)
    have hreplayFirst := trial_program_replay P hmono oracle hpolicy frame store finalStore hvalid hfinalValid
      hzero hkeep R K cut hcut ip.1 ip.2 (smaller ip.1 ip.2) (hold ip.1 ip.2) prior first firstTrace hfirst hfirstFinal
    have hreplayTail := ih first.store hfirstValid hfirstFinal hsmall' (prior ++ firstTrace)
      tail tailTrace htail hresultKeep
    change (prefer first.output tail.output).map (fun s => s.realize R K) = _
    rw [prefer_map, hreplayFirst, hreplayTail]
    rw [List.map_cons, firstSome_cons]

/-- The actual all-pairs physical stage reproduces the existing hungry
`searchStage` exactly, with all cache entries mapped by the same realization. -/
theorem stage_program_replay {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store finalStore : Store n)
    (hvalid : ValidStore P frame store) (hfinalValid : ValidStore P frame finalStore)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hkeep : ∀ q, (store q).Sublist (finalStore q))
    (R : StoreRealization frame finalStore) (K : Core.Memo.Key n (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (hcut : Core.CutSpec (Core.Memo.restrict R.costs K) cut)
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hold : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) (result : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (hrun : Executes oracle (stageProgram frame store K smaller) prior result trace)
    (hresultKeep : ∀ q, (result.store q).Sublist (finalStore q)) :
    result.output.map (fun s => s.realize R K) = Core.searchStage (Core.Memo.restrict R.costs K) cut
      (fun i p => (smaller i p).map (fun s => s.realize R (Core.Memo.remove K i p))) := by
  exact trials_program_replay P hmono oracle hpolicy frame store finalStore hvalid hfinalValid hzero hkeep R K
    cut hcut smaller hold _ prior result trace hrun hresultKeep

end EnvyFreeResearch.Full.Chores.PhysicalCore
