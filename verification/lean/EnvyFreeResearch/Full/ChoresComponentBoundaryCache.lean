import EnvyFreeResearch.Full.ChoresComponentBoundaryIntervalScope

/-! Actual Eval-only cache refinement cannot invent endpoints: it retains
old ones or splits at the explicitly supplied coordinate. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

def CacheKnown (points : Set ℝ) (cache : List (Parent n)) : Prop :=
  ∀ p ∈ cache, ParentKnown points p

theorem CacheKnown.mono {old more : Set ℝ} {cache : List (Parent n)}
    (h : CacheKnown old cache) (hm : old ⊆ more) : CacheKnown more cache :=
  fun p hp => ⟨hm (h p hp).1, hm (h p hp).2⟩

theorem inherited_cache_known (P : Profile (Fin n)) (cache : List (Parent n))
    (hv : Valid P cache) (ho : Ordered cache) : CacheKnown {x | Aligned cache x} cache := by
  intro p hp
  exact ⟨inherited_left_aligned P hv ho hp, inherited_right_aligned P hv ho hp⟩

theorem align_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (x : ℝ) (hx : x ∈ points) (cache : List (Parent n))
    (hold : CacheKnown points cache) (prior : History (Query (Fin n)) ℝ)
    (fresh : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (alignProgram x cache) prior fresh trace) :
    CacheKnown points fresh ∧ Scoped points trace := by
  induction cache generalizing prior fresh trace with
  | nil =>
    cases h
    exact ⟨by simp [CacheKnown], trivial⟩
  | cons p ps ih =>
    have hp := hold p List.mem_cons_self
    have hps : CacheKnown points ps := fun q hq => hold q (List.mem_cons_of_mem _ hq)
    by_cases hinterior : p.left < x ∧ x < p.right
    · simp only [alignProgram, ite_eq_left hinterior] at h
      obtain ⟨values, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      refine ⟨?_, values_scoped oracle points p.left x hp.1 hx _ prior values first hfirst⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hp.1, hx⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hx, hp.2⟩
        · exact hps q hq
    · simp only [alignProgram, ite_eq_right hinterior] at h
      obtain ⟨tail, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      obtain ⟨hknown, hscope⟩ := ih hps prior tail first hfirst
      refine ⟨?_, hscope⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hknown q hq

theorem align_many_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (known : Set ℝ) (points : List ℝ) (hpoints : ∀ x ∈ points, x ∈ known)
    (cache : List (Parent n)) (hold : CacheKnown known cache)
    (prior : History (Query (Fin n)) ℝ) (fresh : List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (alignManyProgram points cache) prior fresh trace) :
    CacheKnown known fresh ∧ Scoped known trace := by
  induction points generalizing cache prior fresh trace with
  | nil => cases h; exact ⟨hold, trivial⟩
  | cons x rest ih =>
    obtain ⟨first, t₁, t₂, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
    subst trace
    obtain ⟨hknown, hscope⟩ := align_known oracle known x (hpoints x List.mem_cons_self)
      cache hold prior first t₁ hfirst
    obtain ⟨htknown, htscope⟩ := ih (fun y hy => hpoints y (List.mem_cons_of_mem _ hy))
      first hknown (prior ++ t₁) fresh t₂ hsecond
    exact ⟨htknown, (scoped_append known t₁ t₂).mpr
      ⟨hscope, htscope.mono subset_union_left⟩⟩

/-- The paid return recorder preserves the original old-or-Cut provenance of
all resulting cache boundaries and of every one of its Eval endpoints. -/
theorem record_known (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (cache : List (Parent n)) (hv : Valid P cache) (ho : Ordered cache)
    (points : List ℝ) (source : History (Query (Fin n)) ℝ)
    (hsource : ∀ x ∈ points, FromTrace cache source x)
    (prior : History (Query (Fin n)) ℝ) (fresh : List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (recordProgram cache points) prior fresh trace) :
    CacheKnown (Known {x | Aligned cache x} source) fresh ∧
      Scoped (Known {x | Aligned cache x} source) trace := by
  apply align_many_known oracle (Known {x | Aligned cache x} source)
    (freshPoints cache points).toList _ cache
    ((inherited_cache_known P cache hv ho).mono subset_union_left) prior fresh trace h
  intro x hx
  exact hsource x ((mem_freshPoints cache points x).mp (Finset.mem_toList.mp hx)).1

end EnvyFreeResearch.Full.Chores.Boundary
