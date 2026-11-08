import EnvyFreeResearch.Full.ChoresComponentBoundaryCoreScope
import EnvyFreeResearch.Full.ChoresComponentBoundaryInitial

/-! The complete interval Core's endpoint discipline is proved directly from
its query program, independently of its semantic correctness theorem. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent PhysicalCore
open scoped Classical

variable {n : ℕ}

theorem values_scoped (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points) (agents : List (Fin n))
    (prior : History (Query (Fin n)) ℝ) (out : Fin n → ℝ) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (valuesProgram a b agents) prior out trace) : Scoped points trace := by
  induction agents generalizing prior out trace with
  | nil => cases h; trivial
  | cons i rest ih =>
    cases h with
    | ask q next prior reply out tail hreply hnext =>
      obtain ⟨values, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ hnext
      cases hsecond
      simp only [List.append_nil] at htrace
      subst tail
      refine ⟨⟨ha, hb⟩, ?_⟩
      rw [known_eval]
      exact ih _ values first hfirst

theorem cut_parents_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (target : ℝ) (k : ℕ) (a b : ℝ)
    (ha : a ∈ points) (hb : b ∈ points) (remaining : Fin n → ℝ)
    (prior : History (Query (Fin n)) ℝ) (out : List (Parent n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (cutParentsProgram c target k a b remaining) prior out trace) : Scoped points trace := by
  induction k generalizing points a b remaining prior out trace with
  | zero => cases h; trivial
  | succ k ih =>
    obtain ⟨record, first, second, hfirst, hrest, htrace⟩ := Executes.split_bind _ _ h
    obtain ⟨parents, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hrest
    cases hreturn
    simp only [List.append_nil] at hsecond
    subst second
    subst trace
    have hpoint : record.point ∈ Known points first :=
      Or.inr (endpoint_from_trace oracle c a b target prior record first hfirst)
    exact (scoped_append points first tail).mpr ⟨
      endpoint_scoped oracle points c a b target ha hb prior record first hfirst,
      ih (Known points first) record.point b hpoint (Or.inl hb) _
        (prior ++ first) parents tail htail⟩

theorem initial_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : InitialPartition.Outcome n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (initialProgram c a b) prior out trace) : Scoped points trace := by
  obtain ⟨total, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  have hf := values_scoped oracle points a b ha hb _ prior total first hfirst
  by_cases hz : ∃ i, total i = 0
  · simp only [dite_eq_left hz] at hsecond
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact hf
  · simp only [dite_eq_right hz] at hsecond
    obtain ⟨parents, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hsecond
    cases hreturn
    simp only [List.append_nil] at hsecond
    subst second
    subst trace
    exact (scoped_append points first tail).mpr ⟨hf,
      cut_parents_scoped oracle (Known points first) c _ (n - 1) a b
        (Or.inl ha) (Or.inl hb) total (prior ++ first) parents tail htail⟩

theorem core_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : IntervalCore.Outcome n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (IntervalCore.coreProgram c a b) prior out trace) : Scoped points trace := by
  obtain ⟨initial, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  have hf := initial_scoped oracle points c a b ha hb prior initial first hfirst
  have hipoints := initial_known oracle points c a b ha hb prior initial first hfirst
  cases initial with
  | zero i =>
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact hf
  | partition total parents =>
    by_cases hlen : parents.length = n
    · let parent := indexed parents hlen
      have hpknown : ∀ p, ParentKnown (Known points first) (parent p) :=
        fun p => hipoints _ (indexed_mem parents hlen p)
      let frame := IntervalCore.parentFrame parent
      have hknown : StoreKnown (Known points first) (initialStore frame) := by
        intro p r hr
        rcases (show r = frame.empty p ∨ r = frame.whole p from by simpa [initialStore] using hr) with rfl | rfl
        · exact (hpknown p).1
        · exact (hpknown p).2
      rw [IntervalCore.finishProgram, dite_eq_left hlen] at hsecond
      obtain ⟨result, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hsecond
      cases hreturn
      simp only [List.append_nil] at hsecond
      subst second
      subst trace
      exact (scoped_append points first tail).mpr ⟨hf,
        prefix_scoped oracle (Known points first) frame (initialStore frame) hknown
          (prior ++ first) result tail htail⟩
    · rw [IntervalCore.finishProgram, dite_eq_right hlen] at hsecond
      cases hsecond

end EnvyFreeResearch.Full.Chores.Boundary
