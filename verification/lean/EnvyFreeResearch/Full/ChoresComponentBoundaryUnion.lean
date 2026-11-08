import EnvyFreeResearch.Full.ChoresComponentBoundaryCache

/-! Physical finite-union cutting preserves coordinate provenance, including
cached boundary replies and null components. No valid-target or success
certificate is assumed in these execution-structural statements. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

theorem CacheKnown.filter {points : Set ℝ} {cache : List (Parent n)}
    (h : CacheKnown points cache) (keep : Parent n → Bool) : CacheKnown points (cache.filter keep) :=
  fun p hp => h p (List.mem_filter.mp hp).1

theorem CacheKnown.append {points : Set ℝ} {first second : List (Parent n)}
    (hf : CacheKnown points first) (hs : CacheKnown points second) : CacheKnown points (first ++ second) := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hf p) (hs p)

theorem endpoint_known (points : Set ℝ) (a : ℝ) (ha : a ∈ points)
    (cache : List (Parent n)) (h : CacheKnown points cache) : endpoint a cache ∈ points := by
  induction cache generalizing a with
  | nil => exact ha
  | cons p ps ih =>
    exact ih p.right (h p List.mem_cons_self).2 (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem split_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (t : ℝ) (cache : List (Parent n))
    (hold : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (out : Split n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (splitProgram c t cache) prior out trace) :
    CacheKnown (Known points trace) (out.prefixParts ++ out.suffixParts) ∧ Scoped points trace := by
  induction cache generalizing t prior out trace with
  | nil =>
    cases h
    exact ⟨by simp [CacheKnown], trivial⟩
  | cons p ps ih =>
    have hp := hold p List.mem_cons_self
    have hps : CacheKnown points ps := fun q hq => hold q (List.mem_cons_of_mem _ hq)
    by_cases ht : t = 0
    · simp only [splitProgram, ite_eq_left ht] at h
      cases h
      exact ⟨hold.mono subset_union_left, trivial⟩
    · by_cases hwhole : p.value c ≤ t
      · simp only [splitProgram, ite_eq_right ht, ite_eq_left hwhole] at h
        obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
        cases hsecond
        simp only [List.append_nil] at htrace
        subst trace
        obtain ⟨hnew, hs⟩ := ih _ hps prior result first hfirst
        refine ⟨?_, hs⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨Or.inl hp.1, Or.inl hp.2⟩
        · exact hnew q hq
      · simp only [splitProgram, ite_eq_right ht, ite_eq_right hwhole] at h
        obtain ⟨record, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
        cases hsecond
        simp only [List.append_nil] at htrace
        subst trace
        have hx : record.point ∈ Known points first :=
          Or.inr (endpoint_from_trace oracle c p.left p.right t prior record first hfirst)
        refine ⟨?_, endpoint_scoped oracle points c p.left p.right t hp.1 hp.2 prior record first hfirst⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨Or.inl hp.1, hx⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hx, Or.inl hp.2⟩
          · exact ⟨Or.inl (hps q hq).1, Or.inl (hps q hq).2⟩

theorem suffix_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (t : ℝ) (cache : List (Parent n))
    (hold : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (out : SuffixSplit n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (suffixProgram c t cache) prior out trace) :
    CacheKnown (Known points trace) (out.prefixParts ++ out.suffixParts) ∧ Scoped points trace := by
  obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hsecond
  simp only [List.append_nil] at htrace
  subst trace
  exact split_known oracle points c _ cache hold prior result first hfirst

theorem restricted_cut_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a t : ℝ) (ha : a ∈ points) (cache : List (Parent n))
    (hold : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (out : RestrictedCutResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (restrictedCutProgram c a t cache) prior out trace) :
    CacheKnown (Known points trace) (out.parts.prefixParts ++ out.parts.suffixParts) ∧
      Scoped points trace ∧ out.point ∈ Known points trace := by
  obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hsecond
  simp only [List.append_nil] at htrace
  subst trace
  obtain ⟨hcache, hscope⟩ := split_known oracle points c t cache hold prior result first hfirst
  exact ⟨hcache, hscope, endpoint_known (Known points first) a (Or.inl ha) result.prefixParts
    (fun p hp => hcache p (List.mem_append_left _ hp))⟩

theorem query_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : List (Parent n)) (hold : CacheKnown points cache)
    (q : Query (Fin n)) (hq : BoundsIn points q) (prior : History (Query (Fin n)) ℝ)
    (out : QueryResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (queryProgram cache q) prior out trace) :
    CacheKnown (Known points trace) out.cache ∧ Scoped points trace ∧
      (isCutQuery q = true → out.reply ∈ Known points trace) := by
  cases q with
  | eval i a b =>
    cases h
    exact ⟨hold.mono subset_union_left, trivial, by simp [isCutQuery]⟩
  | cut i a b t =>
    obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    obtain ⟨hcache, hscope, hpoint⟩ := restricted_cut_known oracle points i a t hq.1
      (window a b cache) (hold.filter _) prior result first hfirst
    refine ⟨?_, hscope, fun _ => hpoint⟩
    exact ((hold.filter _).mono subset_union_left).append
      (hcache.append ((hold.filter _).mono subset_union_left))

theorem checked_query_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : List (Parent n)) (hold : CacheKnown points cache)
    (q : Query (Fin n)) (hq : BoundsIn points q) (prior : History (Query (Fin n)) ℝ)
    (out : OracleResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (checkedQueryProgram cache q) prior out trace) :
    CacheKnown (Known points trace) out.cache ∧ Scoped points trace ∧
      (∀ r, out.reply = some r → isCutQuery q = true → r ∈ Known points trace) := by
  by_cases ht : ValidTarget cache q
  · simp only [checkedQueryProgram, ite_eq_left ht] at h
    obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    obtain ⟨hcache, hscope, hpoint⟩ := query_known oracle points cache hold q hq prior result first hfirst
    exact ⟨hcache, hscope, fun r hr hc => Option.some.inj hr ▸ hpoint hc⟩
  · simp only [checkedQueryProgram, ite_eq_right ht] at h
    cases h
    exact ⟨hold.mono subset_union_left, trivial, fun r hr => by cases hr⟩

theorem full_query_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (cache : List (Parent n)) (hold : CacheKnown points cache)
    (q : Query (Fin n)) (hq : BoundsIn points q) (prior : History (Query (Fin n)) ℝ)
    (out : OracleResult n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (fullQueryProgram cache q) prior out trace) :
    CacheKnown (Known points trace) out.cache ∧ Scoped points trace ∧
      (∀ r, out.reply = some r → isCutQuery q = true → r ∈ Known points trace) := by
  have hb : queryLeft q ∈ points ∧ queryRight q ∈ points := by cases q <;> exact hq
  by_cases hg : Geometry q
  · simp only [fullQueryProgram, ite_eq_left hg] at h
    obtain ⟨first, t₁, tail, hfirst, htail, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨second, t₂, t₃, hsecond, hthird, htailtrace⟩ := Executes.split_bind _ _ htail
    subst tail
    subst trace
    obtain ⟨hcache₁, hscope₁⟩ := align_known oracle points (queryLeft q) hb.1 cache hold prior first t₁ hfirst
    obtain ⟨hcache₂, hscope₂⟩ := align_known oracle points (queryRight q) hb.2 first hcache₁
      (prior ++ t₁) second t₂ hsecond
    obtain ⟨hcache₃, hscope₃, hpoint⟩ := checked_query_known oracle points second hcache₂ q hq
      ((prior ++ t₁) ++ t₂) out t₃ hthird
    have hm : Known points t₃ ⊆ Known points (t₁ ++ (t₂ ++ t₃)) := by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by simp only [cutReplies_append, List.mem_append]; exact Or.inr (Or.inr hx))
    refine ⟨hcache₃.mono hm, ?_, fun r hr hc => hm (hpoint r hr hc)⟩
    apply (scoped_append points t₁ (t₂ ++ t₃)).mpr
    refine ⟨hscope₁, ?_⟩
    have hs : Scoped points (t₂ ++ t₃) := (scoped_append points t₂ t₃).mpr
      ⟨hscope₂, hscope₃.mono subset_union_left⟩
    exact hs.mono subset_union_left
  · simp only [fullQueryProgram, ite_eq_right hg] at h
    cases h
    exact ⟨hold.mono subset_union_left, trivial, fun r hr => by cases hr⟩

end EnvyFreeResearch.Full.Chores.Boundary
