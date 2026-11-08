import EnvyFreeResearch.Full.ChoresComponentBoundaryCore
import EnvyFreeResearch.Full.ChoresComponentBoundaryScope

/-! The complete memoized Core asks only at inherited store coordinates or
earlier Cut replies. Neither successful candidates nor failed explorations
can introduce an unrecorded query endpoint. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent PhysicalCore
open scoped Classical

variable {n k : ℕ}

theorem global_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (store : Store n) (hold : StoreKnown points store)
    (i p : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ)
    (out : StoreResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ensureGlobalProgram store i p target) prior out trace) : Scoped points trace := by
  obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hsecond
  simp only [List.append_nil] at htrace
  subst trace
  exact ensure_scoped oracle points (store p) (hold p) i target prior result first hfirst

theorem trial_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (old : Option (State n k))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (trialProgram frame store K i p old) prior out trace) : Scoped points trace := by
  cases old with
  | none => cases h; trivial
  | some s =>
    by_cases hw : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s)
    · simp only [trialProgram, ite_eq_left hw] at h
      cases h
      trivial
    · simp only [trialProgram, ite_eq_right hw] at h
      obtain ⟨r, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      exact global_scoped oracle points store hold _ _ _ prior r first hfirst

theorem trials_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (trials : List (Fin (k + 1) × Fin (k + 1)))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (trialsProgram frame store K smaller trials) prior out trace) : Scoped points trace := by
  induction trials generalizing points store prior out trace with
  | nil => cases h; trivial
  | cons ip rest ih =>
    obtain ⟨first, t₁, t₂, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨tail, t₃, t₄, htail, hreturn, htrace₂⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at htrace₂
    subst t₂
    subst trace
    have hf := trial_store_known oracle points frame store hold K ip.1 ip.2 _ prior first t₁ hfirst
    exact (scoped_append points t₁ t₃).mpr ⟨
      trial_scoped oracle points frame store hold K ip.1 ip.2 _ prior first t₁ hfirst,
      ih (Known points t₁) first.store hf (prior ++ t₁) _ t₃ htail⟩

theorem stage_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (stageProgram frame store K smaller) prior out trace) : Scoped points trace :=
  trials_scoped oracle points frame store hold K smaller _ prior out trace h

theorem keys_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (previous : Cache n k) (keys : List (Core.Memo.Key n (k + 1)))
    (prior : History (Query (Fin n)) ℝ) (out : LayerResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (keysProgram frame store previous keys) prior out trace) : Scoped points trace := by
  induction keys generalizing points store prior out trace with
  | nil => cases h; trivial
  | cons K rest ih =>
    obtain ⟨first, t₁, t₂, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨tail, t₃, t₄, htail, hreturn, htrace₂⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at htrace₂
    subst t₂
    subst trace
    have hf := stage_store_known oracle points frame store hold K _ prior first t₁ hfirst
    exact (scoped_append points t₁ t₃).mpr ⟨
      stage_scoped oracle points frame store hold K _ prior first t₁ hfirst,
      ih (Known points t₁) first.store hf (prior ++ t₁) _ t₃ htail⟩

theorem layers_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (k : ℕ) (prior : History (Query (Fin n)) ℝ) (out : LayerResult n k)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (layersProgram frame store k) prior out trace) : Scoped points trace := by
  induction k generalizing points store prior trace with
  | zero => cases h; trivial
  | succ k ih =>
    obtain ⟨previous, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
    subst trace
    have hf := layers_store_known oracle points frame store hold k prior previous first hfirst
    exact (scoped_append points first second).mpr ⟨
      ih points store hold prior previous first hfirst,
      keys_scoped oracle (Known points first) frame previous.store hf previous.cache
        _ (prior ++ first) out second hsecond⟩

theorem prefix_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (prior : History (Query (Fin n)) ℝ) (out : PrefixResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (prefixProgram frame store) prior out trace) : Scoped points trace := by
  obtain ⟨table, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hout : lookup table.cache (fullKey n) with
  | none => rw [hout] at hsecond; cases hsecond
  | some state =>
    rw [hout] at hsecond
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact layers_scoped oracle points frame store hold n prior table first hfirst

end EnvyFreeResearch.Full.Chores.Boundary
