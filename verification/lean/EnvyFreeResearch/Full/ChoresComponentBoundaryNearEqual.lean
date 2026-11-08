import EnvyFreeResearch.Full.ChoresComponentBoundaryAssembly
import EnvyFreeResearch.Full.ChoresNearEqualPartition

/-! Physical near-equal refinement uses only inherited component endpoints
and literal Cut replies. Whole-cell coloring creates no further boundary. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n m : ℕ}

theorem equal_grid_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (t : ℝ) (k : ℕ) (cache : List (Parent n))
    (hcache : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (out : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Quantile.equalGrid c t k cache) prior out trace) :
    CacheKnown (Known points trace) out ∧ Scoped points trace := by
  induction k generalizing points cache prior out trace with
  | zero => cases h; exact ⟨by simpa only [known_nil] using hcache, trivial⟩
  | succ k ih =>
    obtain ⟨first, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
    obtain ⟨rest, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
    cases h₄
    simp only [List.append_nil] at ht₂
    subst t₂
    subst trace
    obtain ⟨hparts, hs₁⟩ := split_known oracle points c t cache hcache prior first t₁ h₁
    have hp : CacheKnown (Known points t₁) first.prefixParts :=
      fun p hp => hparts p (List.mem_append_left _ hp)
    have hs : CacheKnown (Known points t₁) first.suffixParts :=
      fun p hp => hparts p (List.mem_append_right _ hp)
    obtain ⟨hrest, hs₃⟩ := ih (Known points t₁) first.suffixParts hs (prior++t₁) rest t₃ h₃
    exact ⟨(hp.mono (known_mono points t₁ t₃)).append
      (by simpa only [known_append] using hrest), (scoped_append points t₁ t₃).mpr ⟨hs₁, hs₃⟩⟩

theorem common_grid_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (K : ℕ) (observers : List (Fin n)) (cache : List (Parent n))
    (hcache : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (out : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Quantile.commonGrid K observers cache) prior out trace) :
    CacheKnown (Known points trace) out ∧ Scoped points trace := by
  induction observers generalizing points cache prior out trace with
  | nil => cases h; exact ⟨by simpa only [known_nil] using hcache, trivial⟩
  | cons c rest ih =>
    obtain ⟨middle, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
    subst trace
    obtain ⟨hm, hs₁⟩ := equal_grid_known oracle points c _ (K-1) cache hcache prior middle t₁ h₁
    obtain ⟨ho, hs₂⟩ := ih (Known points t₁) middle hm (prior++t₁) out t₂ h₂
    exact ⟨by simpa only [known_append] using ho, (scoped_append points t₁ t₂).mpr ⟨hs₁, hs₂⟩⟩

theorem near_equal_positive_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (positive : Finset (Fin n)) (m : ℕ) (hm : 0 < m)
    (cache : List (Parent n)) (hcache : CacheKnown points cache)
    (prior : History (Query (Fin n)) ℝ) (out : NearEqual.Output n m)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (NearEqual.positiveProgram positive m hm cache) prior out trace) :
    CacheKnown (Known points trace) out.grid ∧ Scoped points trace := by
  obtain ⟨fresh, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  exact common_grid_known oracle points _ _ cache hcache prior fresh first hf

theorem near_equal_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (designated : Finset (Fin n)) (m : ℕ) (hm : 0 < m)
    (cache : List (Parent n)) (hcache : CacheKnown points cache)
    (prior : History (Query (Fin n)) ℝ) (out : NearEqual.Output n m)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (NearEqual.program designated m hm cache) prior out trace) :
    CacheKnown (Known points trace) out.grid ∧ Scoped points trace := by
  unfold NearEqual.program at h
  dsimp only at h
  split_ifs at h
  · exact near_equal_positive_known oracle points _ m hm cache hcache prior out trace h
  · cases h
    exact ⟨by simpa only [known_nil] using hcache, trivial⟩

theorem colored_parts_known {Color : Type*} (points : Set ℝ) (cache : List (Parent n))
    (hcache : CacheKnown points cache) (color : Fin cache.length → Color) (j : Color) :
    CacheKnown points (ColorCache.parts cache color j) :=
  fun p hp => hcache p ((ColorCache.parts_sublist cache color j).subset hp)

theorem near_equal_parts_known (points : Set ℝ) (out : NearEqual.Output n m)
    (h : CacheKnown points out.grid) (j : Fin m) : CacheKnown points (out.parts j) :=
  colored_parts_known points out.grid h out.color j

end EnvyFreeResearch.Full.Chores.Boundary
