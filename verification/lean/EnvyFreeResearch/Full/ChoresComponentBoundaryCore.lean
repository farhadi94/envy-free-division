import EnvyFreeResearch.Full.ChoresComponentBoundaryRecord

/-! The entire materialized prefix-Core table introduces only coordinates
returned by physical Cuts. All exploratory trial records remain in this
accounting, regardless of which candidate is finally selected. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent PhysicalCore
open scoped Classical

variable {n k : ℕ}

def StoreKnown (points : Set ℝ) (store : Store n) : Prop :=
  ∀ p r, r ∈ store p → r.point ∈ points

theorem StoreKnown.mono {points more : Set ℝ} {store : Store n}
    (h : StoreKnown points store) (hm : points ⊆ more) : StoreKnown more store :=
  fun p r hr => hm (h p r hr)

theorem global_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (store : Store n) (hold : StoreKnown points store)
    (i p : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ)
    (out : StoreResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ensureGlobalProgram store i p target) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  intro q r hr
  rcases (global_from_trace oracle store i p target prior out trace h).1 q r hr with
    ⟨old, ho, heq⟩ | hcut
  · exact Or.inl (heq ▸ hold q old ho)
  · exact Or.inr hcut

theorem trial_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1)) (i p : Fin (k + 1)) (old : Option (State n k))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (trialProgram frame store K i p old) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  cases old with
  | none =>
    cases h
    simpa only [known_nil] using hold
  | some s =>
    by_cases hw : recordLE ((frame.whole (K.2 p)).formal (K.1 i)) (target frame K i p s)
    · simp only [trialProgram, ite_eq_left hw] at h
      cases h
      simpa only [known_nil] using hold
    · simp only [trialProgram, ite_eq_right hw] at h
      obtain ⟨r, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      exact global_store_known oracle points store hold _ _ _ prior r first hfirst

theorem trials_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (trials : List (Fin (k + 1) × Fin (k + 1)))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (trialsProgram frame store K smaller trials) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  induction trials generalizing points store prior out trace with
  | nil =>
    cases h
    simpa only [known_nil] using hold
  | cons ip rest ih =>
    obtain ⟨first, t₁, t₂, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨tail, t₃, t₄, htail, hreturn, htrace₂⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at htrace₂
    subst t₂
    subst trace
    have hf := trial_store_known oracle points frame store hold K ip.1 ip.2 _ prior first t₁ hfirst
    have ht := ih (Known points t₁) first.store hf (prior ++ t₁) _ t₃ htail
    simpa only [known_append] using ht

theorem stage_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (prior : History (Query (Fin n)) ℝ) (out : TrialResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (stageProgram frame store K smaller) prior out trace) :
    StoreKnown (Known points trace) out.store :=
  trials_store_known oracle points frame store hold K smaller _ prior out trace h

theorem keys_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (previous : Cache n k) (keys : List (Core.Memo.Key n (k + 1)))
    (prior : History (Query (Fin n)) ℝ) (out : LayerResult n (k + 1))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (keysProgram frame store previous keys) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  induction keys generalizing points store prior out trace with
  | nil =>
    cases h
    simpa only [known_nil] using hold
  | cons K rest ih =>
    obtain ⟨first, t₁, t₂, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨tail, t₃, t₄, htail, hreturn, htrace₂⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at htrace₂
    subst t₂
    subst trace
    have hf := stage_store_known oracle points frame store hold K _ prior first t₁ hfirst
    have ht := ih (Known points t₁) first.store hf (prior ++ t₁) _ t₃ htail
    simpa only [known_append] using ht

theorem layers_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (k : ℕ) (prior : History (Query (Fin n)) ℝ) (out : LayerResult n k)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (layersProgram frame store k) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  induction k generalizing points store prior trace with
  | zero =>
    cases h
    simpa only [known_nil] using hold
  | succ k ih =>
    obtain ⟨previous, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
    subst trace
    have hf := ih points store hold prior previous first hfirst
    have ht := keys_store_known oracle (Known points first) frame previous.store hf previous.cache
      _ (prior ++ first) out second hsecond
    simpa only [known_append] using ht

theorem prefix_store_known
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (frame : Frame n) (store : Store n) (hold : StoreKnown points store)
    (prior : History (Query (Fin n)) ℝ) (out : PrefixResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (prefixProgram frame store) prior out trace) :
    StoreKnown (Known points trace) out.store := by
  obtain ⟨table, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hout : lookup table.cache (fullKey n) with
  | none => rw [hout] at hsecond; cases hsecond
  | some state =>
    rw [hout] at hsecond
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact layers_store_known oracle points frame store hold n prior table first hfirst

end EnvyFreeResearch.Full.Chores.Boundary
